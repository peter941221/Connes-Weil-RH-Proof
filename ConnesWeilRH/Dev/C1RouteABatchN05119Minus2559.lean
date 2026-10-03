import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchN05119MinusPosition2559 : ℝ := (((-65536001) : ℝ) /
        51200000000)

theorem batchN05119MinusZero2559 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchN05119MinusP000Input2559 : RatPair2542 := ((((-((263275 * 10^40
        + 1125171558294111539978267023056917167198) * 10^40
        + 1332055800215011207425642192228936552933)) : ℚ) /
        ((280832 * 10^40
        + 7075746226385963181093901624406268978286) * 10^40
        + 887058614369032185159794907545600000000)),
    ((362039942185747774262029 : ℚ) /
        230584300921369395200000000))

def batchN05119MinusP000Center2559 : RatPair2542 := (((136675650344030269252347073071421939 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((859099660751348423613761077509565 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)))

def batchN05119MinusP000Factor2559 : RatPair2542 := ((((((((((((((9622313004829357499162748658929
    * 10^40
        + 8725117790511638265419544677651216302403) * 10^40
        + 314494830576253981793203093536460219038) * 10^40
        + 3934002373350265522955181951013828198318) * 10^40
        + 1291406450005021260655298118584464582346) * 10^40
        + 1939252574107632021982283154445491389649) * 10^40
        + 3938677821232096984542947886742663381078) * 10^40
        + 6510416019744433035145519177630080595283) * 10^40
        + 1993609979524776862376706283559601140091) * 10^40
        + 8111296510653547575171603819878624272797) * 10^40
        + 4256090981710107127765596357439319612497) * 10^40
        + 9209008623872313536489344599387488400001) : ℚ) /
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
    ((((((((((27759870158043532919 * 10^40
        + 6340614018688992000595408234259737507396) * 10^40
        + 7772172701399559497489308003159937449614) * 10^40
        + 4200960905706384783947409390674546199729) * 10^40
        + 1676422298977617368331659385289718121075) * 10^40
        + 3230828867447227858196979242157250753654) * 10^40
        + 7377638394264238105957395137786328097188) * 10^40
        + 9442871844872692480305021575184926217293) * 10^40
        + 7873637731249801121014012535845083751631) : ℚ) /
        ((((((((451171493800433 * 10^40
        + 289310041348490574715548455196098577920) * 10^40
        + 7902636938171920959638026447709632006500) * 10^40
        + 7648518850311379011259907846647491564509) * 10^40
        + 3217737556976305284719759745611858997651) * 10^40
        + 3266682424345183093751973875588009603237) * 10^40
        + 4753263076802061328706310558860155993222) * 10^40
        + 9798697653014872404551590343080216518117) * 10^40
        + 7295575607033607306793751502848708837376)))

noncomputable def batchN05119MinusP000Error2559 : ℝ := ((6448820903775322072938171961219 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN05119MinusP000BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP000Center2559‖ ≤ batchN05119MinusP000Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP000Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP000Input2559]
  have hs : compactExp2547 batchN05119MinusP000Input2559 5 =
      (batchN05119MinusP000Center2559, ((6448820903775322072938171961219 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP000Input2559 5).2 : ℝ) =
      batchN05119MinusP000Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP000Error2559]
  have h := compactExp_error2547 batchN05119MinusP000Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP000Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP000Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP000DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP000Factor2559 * embedPair2542 batchN05119MinusP000Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP000Factor2559 : ℝ) * batchN05119MinusP000Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
      (storedWidth ⟨0, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP000Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP000Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨0, by omega⟩) (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP000BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP000Factor2559)

def batchN05119MinusP001Input2559 : RatPair2542 := ((((-((337 * 10^40
        + 2581669391407268959104378187086677265835) * 10^40
        + 8255161039993466428760315913304611097119)) : ℚ) /
        ((359 * 10^40
        + 7496679727649814571508006900477875828255) * 10^40
        + 3938416230131927613294794771660800000000)),
    ((362039942185747774262029 : ℚ) /
        230584300921369395200000000))

def batchN05119MinusP001Center2559 : RatPair2542 := (((34169022331674657308501850392852931 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((6872819360454070563190395423926039 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP001Factor2559 : RatPair2542 := ((((((((((((((1586973135704 * 10^40
        + 3486607486185898574687982911025268326212) * 10^40
        + 2869135329435932691138474826257388073611) * 10^40
        + 1911501647430829986572372494144031302110) * 10^40
        + 8453444958739501620022168546090679958577) * 10^40
        + 2423072403032304513234709363502699904850) * 10^40
        + 4114744304014364134300977132049588846091) * 10^40
        + 8585037820802765275451833060515704676625) * 10^40
        + 8794780003170938801879204528513887530109) * 10^40
        + 9797320174701229532329067602891318674443) * 10^40
        + 5437522257941323601016011165702777542173) * 10^40
        + 1503588084036289678560920871877837152187) : ℚ) /
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
    ((((((((((24730436 * 10^40
        + 4624046282149436285103261514750942940540) * 10^40
        + 4841188264791419745500791526187110852763) * 10^40
        + 2664472476424349910446935215805602339458) * 10^40
        + 6413869668777431010776838775867673889746) * 10^40
        + 746189601036691731470013012655278337403) * 10^40
        + 1923673542004935899166395590798039029996) * 10^40
        + 3649561323584268186833113748127201678287) * 10^40
        + 8602545746705995895248953248875059443477) : ℚ) /
        ((((((((404 * 10^40
        + 9778364762535834489062983402079652472870) * 10^40
        + 3798373737324381507248095467743663749494) * 10^40
        + 2113004835996725252119258181634413046350) * 10^40
        + 6272275210159077923488246418401714092448) * 10^40
        + 5028575476107494260550002253111228146223) * 10^40
        + 1584573805121281140132696312080425708340) * 10^40
        + 6811623972839899371827609281611885188981) * 10^40
        + 6480975396836903085471284056881618747392)))

noncomputable def batchN05119MinusP001Error2559 : ℝ := ((6448840969194396923224843774095 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN05119MinusP001BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP001Center2559‖ ≤ batchN05119MinusP001Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP001Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP001Input2559]
  have hs : compactExp2547 batchN05119MinusP001Input2559 5 =
      (batchN05119MinusP001Center2559, ((6448840969194396923224843774095 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP001Input2559 5).2 : ℝ) =
      batchN05119MinusP001Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP001Error2559]
  have h := compactExp_error2547 batchN05119MinusP001Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP001Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP001Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP001DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP001Factor2559 * embedPair2542 batchN05119MinusP001Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP001Factor2559 : ℝ) * batchN05119MinusP001Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP001Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP001Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP001BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP001Factor2559)

def batchN05119MinusP002Input2559 : RatPair2542 := ((((-((8811 * 10^40
        + 7974475504972435624923961780003357186703) * 10^40
        + 8778883137590559728133612891529783413279)) : ℚ) /
        ((9399 * 10^40
        + 4503095778906693550996648513930263830566) * 10^40
        + 1627135197619074312716716346572800000000)),
    (((-362039942185747774262029) : ℚ) /
        230584300921369395200000000))

def batchN05119MinusP002Center2559 : RatPair2542 := (((68338158254347080611939487125973925 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-3436415392202059335222155730840303) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchN05119MinusP002Factor2559 : RatPair2542 := ((((((((((((((506863419787791313073 * 10^40
        + 1611471873584466295358761143940573849135) * 10^40
        + 7885646726073204852153242343683043847653) * 10^40
        + 4593145956214659937638184284738989344589) * 10^40
        + 1730118169380788761957733081075742202945) * 10^40
        + 5051199018744113748769116366188527678667) * 10^40
        + 4858509190392680476623188393710916543904) * 10^40
        + 3082768457098498421754186881538124017472) * 10^40
        + 985151259180164036147189718677361695936) * 10^40
        + 2589862463455666228539434738841480571321) * 10^40
        + 8152423097680421018062222520360786946767) * 10^40
        + 365240878678704216489614615158376718267) : ℚ) /
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
    (((-((((((((11479824069954 * 10^40
        + 484772488544589335107766863461745668200) * 10^40
        + 3696845500945281849942173361744454679886) * 10^40
        + 4842348902401051484115869508799915523584) * 10^40
        + 3603214075261214823017477592657854068500) * 10^40
        + 320461276283109026783724308199533637153) * 10^40
        + 640536687407844406425040491441664750550) * 10^40
        + 5620846443140198914111270217316218319603) * 10^40
        + 4029017111666038514455401882615658411797)) : ℚ) /
        ((((((((188729362 * 10^40
        + 9819701407096191560439935783291819054518) * 10^40
        + 8477595831999746647809341592274305718131) * 10^40
        + 9925177843627926099243621853950442755649) * 10^40
        + 5197984368996465942067804059686875119529) * 10^40
        + 8427309759846740873593659754282592053766) * 10^40
        + 5419148084508808669851942799006996342341) * 10^40
        + 5593321501482920662721494915137035796268) * 10^40
        + 8717394773851440839659151793766229082112)))

noncomputable def batchN05119MinusP002Error2559 : ℝ := ((3224425676717443754085083480953 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN05119MinusP002BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP002Center2559‖ ≤ batchN05119MinusP002Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP002Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP002Input2559]
  have hs : compactExp2547 batchN05119MinusP002Input2559 5 =
      (batchN05119MinusP002Center2559, ((3224425676717443754085083480953 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP002Input2559 5).2 : ℝ) =
      batchN05119MinusP002Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP002Error2559]
  have h := compactExp_error2547 batchN05119MinusP002Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP002Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP002Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP002DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP002Factor2559 * embedPair2542 batchN05119MinusP002Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP002Factor2559 : ℝ) * batchN05119MinusP002Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP002Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP002Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP002BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP002Factor2559)

def batchN05119MinusP003Input2559 : RatPair2542 := ((((-((1163809 * 10^40
        + 2803467370453462244264746520956969698628) * 10^40
        + 520753972540498124346843478850030302933)) : ℚ) /
        ((1241422 * 10^40
        + 9791856163289381605629288925280480441376) * 10^40
        + 2180804704512656185159794907545600000000)),
    (((-362039942185747774262029) : ℚ) /
        230584300921369395200000000))

def batchN05119MinusP003Center2559 : RatPair2542 := (((68338221762420089606593694935436785 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-3436418585734416542388178396647095) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchN05119MinusP003Factor2559 : RatPair2542 :=
    ((((((((((((((72796218840117637389971725810279927 *
    10^40
        + 9369712585336053604037286282352182543883) * 10^40
        + 9743088029793985969084302952271896966186) * 10^40
        + 747398301575641454093907965189143554101) * 10^40
        + 9535463906479862559698530155080290370871) * 10^40
        + 3784310889661480596899274328451803813426) * 10^40
        + 8348749988792410277034150989634476309406) * 10^40
        + 3216070955277341232865446040871106285124) * 10^40
        + 6707934760204328598440997110881672273429) * 10^40
        + 382027527489548044146496947222915263553) * 10^40
        + 6317096014485517908763688144315893659393) * 10^40
        + 647648674191258439276288823020300900001) : ℚ) /
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
    (((-((((((((3485366673305004409934 * 10^40
        + 7491660718333008716826682835303839246176) * 10^40
        + 2459186965421857630832237573501423486529) * 10^40
        + 201950932124449389421920251407519364833) * 10^40
        + 1753069558194068977943060656301149068641) * 10^40
        + 6286879568128623684803432500010964953059) * 10^40
        + 7234399064928511418814110963184846264977) * 10^40
        + 2330172184136725955152762230926150069309) * 10^40
        + 4595234068640798133221396851141069583877)) : ℚ) /
        ((((((((57426026769915242 * 10^40
        + 37248946281463179392937859438651564878) * 10^40
        + 6256287755500187344152790019685904898087) * 10^40
        + 778170784074725160988492459117342265649) * 10^40
        + 1100737857569196410743207737374255904533) * 10^40
        + 390936219895805152906399800831493675186) * 10^40
        + 2352201066425665208458231269990101653944) * 10^40
        + 7115000230235373679619827557598974524932) * 10^40
        + 5176876822868632705495303834282902945792)))

noncomputable def batchN05119MinusP003Error2559 : ℝ := ((6448857159203737902251197562095 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN05119MinusP003BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP003Center2559‖ ≤ batchN05119MinusP003Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP003Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP003Input2559]
  have hs : compactExp2547 batchN05119MinusP003Input2559 5 =
      (batchN05119MinusP003Center2559, ((6448857159203737902251197562095 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP003Input2559 5).2 : ℝ) =
      batchN05119MinusP003Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP003Error2559]
  have h := compactExp_error2547 batchN05119MinusP003Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP003Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP003Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP003DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP003Factor2559 * embedPair2542 batchN05119MinusP003Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP003Factor2559 : ℝ) * batchN05119MinusP003Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP003Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP003Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP003BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP003Factor2559)

def batchN05119MinusP004Input2559 : RatPair2542 := ((((-((20219 * 10^40
        + 5286412261941775910972762094659285731921) * 10^40
        + 6451931165132029084895488306568845913279)) : ℚ) /
        ((21567 * 10^40
        + 9565109682248283934361041297228882745944) * 10^40
        + 4559280761265714312716716346572800000000)),
    ((362039942185747774262029 : ℚ) /
        230584300921369395200000000))

def batchN05119MinusP004Center2559 : RatPair2542 := (((68338259500788089704072508966229503 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((6872840966850856388607695027437749 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP004Factor2559 : RatPair2542 := ((((((((((((((74240892017073084473619 * 10^40
        + 9729822336589976861360036578307381979283) * 10^40
        + 3915059188868638748954489004457108797754) * 10^40
        + 653939806774864964409974431759578722377) * 10^40
        + 352980024715676397560774564441601579864) * 10^40
        + 8432246267827772972272449493359398198733) * 10^40
        + 1583621546500327773978341438159460003862) * 10^40
        + 9541653954249616323477191793370842127987) * 10^40
        + 7703799971464257251100498085168088964084) * 10^40
        + 2625920779396077097476089517526693535347) * 10^40
        + 1454772459206820715621997137869080535934) * 10^40
        + 6729334133071740537391441910080251718267) : ℚ) /
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
    ((((((((((317129202836926 * 10^40
        + 8013915434124467838822447556990103651533) * 10^40
        + 170697515926610612081796648959865436766) * 10^40
        + 1914524657773256300123539802116447827874) * 10^40
        + 8592731175160253215059910523523025510887) * 10^40
        + 8743019570677970777085925253008654715127) * 10^40
        + 4074250847307739593106694531081459623311) * 10^40
        + 5747788552936185350519620420877230422479) * 10^40
        + 2239195631458735096608168581834408411797) : ℚ) /
        ((((((((5231974822 * 10^40
        + 6906096713019726877942647176479129866244) * 10^40
        + 6662510641073731573846327264297890137098) * 10^40
        + 5179996429186788767012609795602587845298) * 10^40
        + 3094043366723476417559808317780461020908) * 10^40
        + 8395394464568485210476066080501681500556) * 10^40
        + 9590758151795896500712782863622381730739) * 10^40
        + 5646541376728787547171188043564357479665) * 10^40
        + 4615360855713682874961551793766229082112)))

noncomputable def batchN05119MinusP004Error2559 : ℝ := ((3224430304581276660804530147649 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN05119MinusP004BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP004Center2559‖ ≤ batchN05119MinusP004Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP004Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP004Input2559]
  have hs : compactExp2547 batchN05119MinusP004Input2559 5 =
      (batchN05119MinusP004Center2559, ((3224430304581276660804530147649 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP004Input2559 5).2 : ℝ) =
      batchN05119MinusP004Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP004Error2559]
  have h := compactExp_error2547 batchN05119MinusP004Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP004Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP004Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP004DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP004Factor2559 * embedPair2542 batchN05119MinusP004Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP004Factor2559 : ℝ) * batchN05119MinusP004Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP004Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP004Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP004BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP004Factor2559)

def batchN05119MinusP005Input2559 : RatPair2542 := ((((-((960037 * 10^40
        + 6342012607625608885787797769382884372499) * 10^40
        + 345329265333619955745170436550090908799)) : ℚ) /
        ((1024061 * 10^40
        + 7791750441362503302291019533199172422902) * 10^40
        + 8340041887645616555479384722636800000000)),
    ((0 : ℚ) /
        1))

def batchN05119MinusP005Center2559 : RatPair2542 := (((68424262043146243304847327298652041 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def batchN05119MinusP005Factor2559 : RatPair2542 := ((((((((((((((818 * 10^40
        + 1371954178408624650377495471832437394841) * 10^40
        + 6304039854858668020297727212294463252285) * 10^40
        + 9542266383060988338779044192159335894120) * 10^40
        + 3009784636538652245186727655505191917794) * 10^40
        + 2174770324437940741759985009991645249032) * 10^40
        + 4656586169718686607024640511085149081487) * 10^40
        + 4817563141196429767450911582980322985125) * 10^40
        + 2799093606281726875284900513795733975424) * 10^40
        + 1596410090975070445223217499968681377703) * 10^40
        + 7593830377558674260465523761014621622402) * 10^40
        + 7681811504677605772175457138042596268799) : ℚ) /
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

noncomputable def batchN05119MinusP005Error2559 : ℝ := ((3073777350247193428604776321287 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN05119MinusP005BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP005Center2559‖ ≤ batchN05119MinusP005Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP005Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP005Input2559]
  have hs : compactExp2547 batchN05119MinusP005Input2559 5 =
      (batchN05119MinusP005Center2559, ((3073777350247193428604776321287 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP005Input2559 5).2 : ℝ) =
      batchN05119MinusP005Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP005Error2559]
  have h := compactExp_error2547 batchN05119MinusP005Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP005Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP005Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP005DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP005Factor2559 * embedPair2542 batchN05119MinusP005Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP005Factor2559 : ℝ) * batchN05119MinusP005Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
      (storedWidth ⟨5, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP005Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP005Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨5, by omega⟩) (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP005BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP005Factor2559)

def batchN05119MinusP006Input2559 : RatPair2542 := ((((-42948756700390030649865186028202667) : ℚ)
    /
        45812979799416911656822374400000000),
    ((0 : ℚ) /
        1))

def batchN05119MinusP006Center2559 : RatPair2542 := (((17106118510071582424137504584889959 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1))

def batchN05119MinusP006Factor2559 : RatPair2542 := ((((((8796994855202706 * 10^40
        + 3733929183619216769383648482784380903587) * 10^40
        + 4784373152439608926521517667812196336155) * 10^40
        + 2851632063004512973984431046956951021037) : ℚ) /
        (((1613189489073774 * 10^40
        + 7850846335343571448973212773441128977131) * 10^40
        + 2962507789998867944049527356204191909545) * 10^40
        + 6360579062433016208124551624344391831704)),
    ((0 : ℚ) /
        1))

noncomputable def batchN05119MinusP006Error2559 : ℝ := ((12295146304184094802306035054029 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119MinusP006BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP006Center2559‖ ≤ batchN05119MinusP006Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP006Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP006Input2559]
  have hs : compactExp2547 batchN05119MinusP006Input2559 5 =
      (batchN05119MinusP006Center2559, ((12295146304184094802306035054029 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP006Input2559 5).2 : ℝ) =
      batchN05119MinusP006Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP006Error2559]
  have h := compactExp_error2547 batchN05119MinusP006Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP006Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP006Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP006DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP006Factor2559 * embedPair2542 batchN05119MinusP006Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP006Factor2559 : ℝ) * batchN05119MinusP006Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP006Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP006Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP006BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP006Factor2559)

def batchN05119MinusP007Input2559 : RatPair2542 := ((((-((1163809 * 10^40
        + 2803467370453462244264746520956969698628) * 10^40
        + 520753972540498124346843478850030302933)) : ℚ) /
        ((1241422 * 10^40
        + 9791856163289381605629288925280480441376) * 10^40
        + 2180804704512656185159794907545600000000)),
    ((0 : ℚ) /
        1))

def batchN05119MinusP007Center2559 : RatPair2542 := (((34212284074386526062500505013302701 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1))

def batchN05119MinusP007Factor2559 : RatPair2542 := ((((((((((((((18957 * 10^40
        + 1157388124140305658204815997727238531387) * 10^40
        + 8934582703611745691759249239185921468368) * 10^40
        + 3468642117073906671773998471501073964258) * 10^40
        + 1188647923546388889901633883776217532841) * 10^40
        + 5899374176086352559815072947219306068865) * 10^40
        + 9586231445630122703609622353147868041774) * 10^40
        + 6772911569946161522523575487567871498143) * 10^40
        + 3977875724683718323684100848110348687320) * 10^40
        + 6653500277088718501630028600943365013073) * 10^40
        + 7801091191311592463453486273686342610971) * 10^40
        + 6148676952324046171049911745853429491437) : ℚ) /
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

noncomputable def batchN05119MinusP007Error2559 : ℝ := ((3073790671506489248495012638049 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN05119MinusP007BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP007Center2559‖ ≤ batchN05119MinusP007Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP007Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP007Input2559]
  have hs : compactExp2547 batchN05119MinusP007Input2559 5 =
      (batchN05119MinusP007Center2559, ((3073790671506489248495012638049 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP007Input2559 5).2 : ℝ) =
      batchN05119MinusP007Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP007Error2559]
  have h := compactExp_error2547 batchN05119MinusP007Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP007Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP007Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP007DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP007Factor2559 * embedPair2542 batchN05119MinusP007Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP007Factor2559 : ℝ) * batchN05119MinusP007Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP007Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP007Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP007BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP007Factor2559)

def batchN05119MinusP008Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((260739661220379310273297 : ℚ) /
        461168601842738790400000000))

def batchN05119MinusP008Center2559 : RatPair2542 := (((68413135137079552770706605104777515 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((2475792387690418440733645206004697 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP008Factor2559 : RatPair2542 := ((((((((((((((50765734884070974659879817263322
    *
    10^40
        + 7358584619600401839625980549949736218351) * 10^40
        + 322629969631477160736459157880786050097) * 10^40
        + 1577201836503287895777964945384751502134) * 10^40
        + 2823846487623847885487652868124714351690) * 10^40
        + 8609628433264693999157728050183697164089) * 10^40
        + 3895982712984528808822807147989996004833) * 10^40
        + 7246267305709765689148756806891960579399) * 10^40
        + 6371891446473404871391740840439502491431) * 10^40
        + 2512986614287969041813215835843425463624) * 10^40
        + 6895674070277884231737372643057402924723) * 10^40
        + 6479921335086909515793139673683557865209) : ℚ) /
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
    ((((((((((2431577858118515096 * 10^40
        + 6076748170272578184476275644787575356888) * 10^40
        + 980837051023412812081285584295718377543) * 10^40
        + 6627359060893745806614063456549045515189) * 10^40
        + 1838432528467599171991978631317014483416) * 10^40
        + 1719866778256924635203074172900214235243) * 10^40
        + 5348284440452711794797772820814972047669) * 10^40
        + 2479560854122620818732262139797321986078) * 10^40
        + 6816393395597965292579294879147022468887) : ℚ) /
        ((((((((789760565096797 * 10^40
        + 8095510052729368356927070454129803701516) * 10^40
        + 3743019781947976825806172922048722462656) * 10^40
        + 7549517672188252238923971472068227595581) * 10^40
        + 396392107312125827044244572623346852688) * 10^40
        + 4622570372462752472580018727281281253007) * 10^40
        + 5566503809205145580154189391855073684950) * 10^40
        + 8769806980714736530281372283185850359703) * 10^40
        + 7690234925784503979189695810609031938048)))

noncomputable def batchN05119MinusP008Error2559 : ℝ := ((12511161947040972037249728888013 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119MinusP008BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP008Center2559‖ ≤ batchN05119MinusP008Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP008Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP008Input2559]
  have hs : compactExp2547 batchN05119MinusP008Input2559 5 =
      (batchN05119MinusP008Center2559, ((12511161947040972037249728888013 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP008Input2559 5).2 : ℝ) =
      batchN05119MinusP008Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP008Error2559]
  have h := compactExp_error2547 batchN05119MinusP008Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP008Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP008Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP008DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP008Factor2559 * embedPair2542 batchN05119MinusP008Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP008Factor2559 : ℝ) * batchN05119MinusP008Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP008Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP008Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP008BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP008Factor2559)

def batchN05119MinusP009Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((387788191040974601829711 : ℚ) /
        461168601842738790400000000))

def batchN05119MinusP009Center2559 : RatPair2542 := (((68399563841778805320831794557230777 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((920477121588419990933635517418443 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN05119MinusP009Factor2559 : RatPair2542 :=
    ((((((((((((((110445360839335473920836161853223 *
    10^40
        + 4137710787891314458442796505422137975649) * 10^40
        + 7841514523367066844535781640892115237539) * 10^40
        + 2722208161954766361456268191816382344208) * 10^40
        + 3343555329476260066708513612551192858994) * 10^40
        + 338301735796359259249774003480043440585) * 10^40
        + 5840331955567368266771114090336360407785) * 10^40
        + 9637834904406106545492077511638762929028) * 10^40
        + 6845403504959044100104990693569717270739) * 10^40
        + 1222391516345317652882072140284725712351) * 10^40
        + 2719139623943461609214154955471697932226) * 10^40
        + 1849266643476667901950879133782976261177) : ℚ) /
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
    ((((((((((53454951779492547439 * 10^40
        + 4690230425105069758065899426376187080100) * 10^40
        + 2974571939685459666367818310385115378386) * 10^40
        + 9774596909951660177026604223289502222563) * 10^40
        + 6601632308339224357029017710688018157804) * 10^40
        + 850943660287904737071891380878228160619) * 10^40
        + 8718781485786650959934948523802355874243) * 10^40
        + 1154167467968154853387411672216576278128) * 10^40
        + 6643333696125560052029960583147421971839) : ℚ) /
        ((((((((5528323955677584 * 10^40
        + 6668570369105578498489493178908625910614) * 10^40
        + 6201138473635837780643210454341057238597) * 10^40
        + 2846623705317765672467800304477593169067) * 10^40
        + 2774744751184880789309712008363427968819) * 10^40
        + 2357992607239267308060131090968968771052) * 10^40
        + 8965526664436019061079325742985515794656) * 10^40
        + 1388648865003155711969605982300952517926) * 10^40
        + 3831644480491527854327870674263223566336)))

noncomputable def batchN05119MinusP009Error2559 : ℝ := ((12616817366626715925935176043465 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119MinusP009BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP009Center2559‖ ≤ batchN05119MinusP009Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP009Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP009Input2559]
  have hs : compactExp2547 batchN05119MinusP009Input2559 5 =
      (batchN05119MinusP009Center2559, ((12616817366626715925935176043465 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP009Input2559 5).2 : ℝ) =
      batchN05119MinusP009Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP009Error2559]
  have h := compactExp_error2547 batchN05119MinusP009Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP009Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP009Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP009DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP009Factor2559 * embedPair2542 batchN05119MinusP009Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP009Factor2559 : ℝ) * batchN05119MinusP009Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP009Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP009Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP009BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP009Factor2559)

def batchN05119MinusP010Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((230684447942438333698521 : ℚ) /
        230584300921369395200000000))

def batchN05119MinusP010Center2559 : RatPair2542 := (((68389273027037334110125418654915613 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((1095077748882371075366422795709885 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN05119MinusP010Factor2559 : RatPair2542 := ((((((((((((((38925434847874801864695325842905
    *
    10^40
        + 9315557744931820150329663707161297263126) * 10^40
        + 2555327216978029311477721963186838121792) * 10^40
        + 1796661954058346907356753254978354608017) * 10^40
        + 4599020785644286451346153921921185180018) * 10^40
        + 7437529060244691387466012191604088941097) * 10^40
        + 4042422471203645277745337382097107703449) * 10^40
        + 8351623782987801011833361306271311201450) * 10^40
        + 9499023051112538041855797952603137629643) * 10^40
        + 827211429576719987538979048536902485241) * 10^40
        + 3537444237650253465589963543149849670568) * 10^40
        + 9910777906461031429741292126711886723401) : ℚ) /
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
    ((((((((((11123261938591818825 * 10^40
        + 8353948718994151917887379507407834353991) * 10^40
        + 7587070929467247514021424383540507526899) * 10^40
        + 517981686098580096929603428041040694354) * 10^40
        + 5270253886681410368971821101767093345720) * 10^40
        + 3221447168401355707126333293104717598962) * 10^40
        + 4366197088016018600428910015106984631523) * 10^40
        + 3393894860731848903254731765696963605356) * 10^40
        + 5097692643659745244896081517935017442873) : ℚ) /
        ((((((((691040494459698 * 10^40
        + 833571296138197312311186647363578238826) * 10^40
        + 8275142309204479722580401306792632154824) * 10^40
        + 6605827963164720709058475038059699146133) * 10^40
        + 4096843093898110098663714001045428496102) * 10^40
        + 4044749075904908413507516386371121096381) * 10^40
        + 6120690833054502382634915717873189474332) * 10^40
        + 173581108125394463996200747787619064740) * 10^40
        + 7978955560061440981790983834282902945792)))

noncomputable def batchN05119MinusP010Error2559 : ℝ := ((12678122052529378217244052131603 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119MinusP010BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP010Center2559‖ ≤ batchN05119MinusP010Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP010Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP010Input2559]
  have hs : compactExp2547 batchN05119MinusP010Input2559 5 =
      (batchN05119MinusP010Center2559, ((12678122052529378217244052131603 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP010Input2559 5).2 : ℝ) =
      batchN05119MinusP010Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP010Error2559]
  have h := compactExp_error2547 batchN05119MinusP010Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP010Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP010Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP010DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP010Factor2559 * embedPair2542 batchN05119MinusP010Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP010Factor2559 : ℝ) * batchN05119MinusP010Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP010Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP010Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP010BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP010Factor2559)

def batchN05119MinusP011Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((255213677437476200797801 : ℚ) /
        230584300921369395200000000))

def batchN05119MinusP011Center2559 : RatPair2542 := (((136762842509260362310953976544953545 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((4845894537794678362507774612692251 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP011Factor2559 : RatPair2542 := ((((((((((((((47558339539413889738330706675785
    *
    10^40
        + 2423182231994188277989282850611316955052) * 10^40
        + 3660104328283010551181756141844394859933) * 10^40
        + 103496648272296806501173037104408631436) * 10^40
        + 4546664289255016409318211144422387121699) * 10^40
        + 9061567770488822895336559238694805965066) * 10^40
        + 9630833451730334923503622281137179489043) * 10^40
        + 3457612871275066999761825355545246531524) * 10^40
        + 8039990864682715857249999768370333309981) * 10^40
        + 6271408321897894166771723745676486475315) * 10^40
        + 2022603736255678573680981353092350202243) * 10^40
        + 8568000280291969665095413580605625825641) : ℚ) /
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
    ((((((((((14984992057264236199 * 10^40
        + 6226218718884660873269787316623921311885) * 10^40
        + 3306687129771071786609235773054636042268) * 10^40
        + 7429943766285611359639796988815314551345) * 10^40
        + 1724566716301536484988483192767270886212) * 10^40
        + 4057148454619185947167994105683874594420) * 10^40
        + 2170890059040711757186106514800032911781) * 10^40
        + 7482760255387986518527347470938027665419) * 10^40
        + 6408152462070438871769759002775307376873) : ℚ) /
        ((((((((691040494459698 * 10^40
        + 833571296138197312311186647363578238826) * 10^40
        + 8275142309204479722580401306792632154824) * 10^40
        + 6605827963164720709058475038059699146133) * 10^40
        + 4096843093898110098663714001045428496102) * 10^40
        + 4044749075904908413507516386371121096381) * 10^40
        + 6120690833054502382634915717873189474332) * 10^40
        + 173581108125394463996200747787619064740) * 10^40
        + 7978955560061440981790983834282902945792)))

noncomputable def batchN05119MinusP011Error2559 : ℝ := ((12719041660541592984186397425229 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119MinusP011BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP011Center2559‖ ≤ batchN05119MinusP011Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP011Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP011Input2559]
  have hs : compactExp2547 batchN05119MinusP011Input2559 5 =
      (batchN05119MinusP011Center2559, ((12719041660541592984186397425229 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP011Input2559 5).2 : ℝ) =
      batchN05119MinusP011Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP011Error2559]
  have h := compactExp_error2547 batchN05119MinusP011Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP011Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP011Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP011DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP011Factor2559 * embedPair2542 batchN05119MinusP011Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP011Factor2559 : ℝ) * batchN05119MinusP011Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP011Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP011Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP011BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP011Factor2559)

def batchN05119MinusP012Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((5612399119318874813509 : ℚ) /
        4611686018427387904000000))

def batchN05119MinusP012Center2559 : RatPair2542 := (((17093113333274168743473140176742453 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((5328065872176414572945352535907913 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP012Factor2559 : RatPair2542 := ((((((((((((((14354709339007153312970606155845
    *
    10^40
        + 2166880206417054307907767067702941304280) * 10^40
        + 1509499983158017812616632704714194738596) * 10^40
        + 9080031340068480968450518021745723552870) * 10^40
        + 5711719897150947173849997076804907961932) * 10^40
        + 6402806524009722267803902879274306558872) * 10^40
        + 6013338682747630570714751257116249064126) * 10^40
        + 3757319180398227282197411570946230107595) * 10^40
        + 1162111278231782729231725297937502201811) * 10^40
        + 2626775810074429819182581911941621547699) * 10^40
        + 490780891723653114759591642868514838758) * 10^40
        + 7700739615063251675328204854576950900513) : ℚ) /
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
    ((((((((((2480157454108574051 * 10^40
        + 452243255804522322309444010703985456318) * 10^40
        + 4053264057844807603912223093630976128515) * 10^40
        + 6550455028124747554836459928888925431184) * 10^40
        + 8389916241777331790487082209191563715107) * 10^40
        + 2316504462504693660852993921911934487027) * 10^40
        + 5170687636271299724567075896752645236868) * 10^40
        + 166185242952113359226973377707687944289) * 10^40
        + 4351687137512526749930250941689959907925) : ℚ) /
        ((((((((86380061807462 * 10^40
        + 2604196412017274664038898330920447279853) * 10^40
        + 3534392788650559965322550163349079019353) * 10^40
        + 825728495395590088632309379757462393266) * 10^40
        + 6762105386737263762332964250130678562012) * 10^40
        + 8005593634488113551688439548296390137047) * 10^40
        + 7015086354131812797829364464734148684291) * 10^40
        + 5021697638515674307999525093473452383092) * 10^40
        + 5997369445007680122723872979285362868224)))

noncomputable def batchN05119MinusP012Error2559 : ℝ := ((12761462825337725864745839544313 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119MinusP012BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP012Center2559‖ ≤ batchN05119MinusP012Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP012Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP012Input2559]
  have hs : compactExp2547 batchN05119MinusP012Input2559 5 =
      (batchN05119MinusP012Center2559, ((12761462825337725864745839544313 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP012Input2559 5).2 : ℝ) =
      batchN05119MinusP012Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP012Error2559]
  have h := compactExp_error2547 batchN05119MinusP012Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP012Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP012Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP012DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP012Factor2559 * embedPair2542 batchN05119MinusP012Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP012Factor2559 : ℝ) * batchN05119MinusP012Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP012Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP012Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP012BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP012Factor2559)

def batchN05119MinusP013Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((60754466143128272313291 : ℚ) /
        46116860184273879040000000))

def batchN05119MinusP013Center2559 : RatPair2542 := (((68363540785304809174710801069040455 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((5767404118669434242834954134771201 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP013Factor2559 : RatPair2542 := ((((((((((((((67218877050217214410747700978568
    *
    10^40
        + 8075196412193045133888031101118873755778) * 10^40
        + 9152958824756031066492306816980501224899) * 10^40
        + 6578227303155794938388748233813418825179) * 10^40
        + 6799607445082413067832357362217909260992) * 10^40
        + 3649971951843115008887417569036393652396) * 10^40
        + 3595247178783386208144668885382239262480) * 10^40
        + 3727543684200461848022946594254058487481) * 10^40
        + 2638938861517981841526443810055582432141) * 10^40
        + 1683532758772945498893992242950054382736) * 10^40
        + 5036980501383502362852187755689276650681) * 10^40
        + 2080710546838250167973921751938996484777) : ℚ) /
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
    ((((((((((25098033346173512190 * 10^40
        + 3601028419443498795114898330265431823812) * 10^40
        + 708354178863030479128666000127898583519) * 10^40
        + 244115878662809654616071884965331527931) * 10^40
        + 2605795816992036413646183422153834733974) * 10^40
        + 8462442718946977525499902506660514826590) * 10^40
        + 9225597268617950654208776887422319893888) * 10^40
        + 2254091295557366693643190035981332670871) * 10^40
        + 6991547709723431897728554569039623540535) : ℚ) /
        ((((((((691040494459698 * 10^40
        + 833571296138197312311186647363578238826) * 10^40
        + 8275142309204479722580401306792632154824) * 10^40
        + 6605827963164720709058475038059699146133) * 10^40
        + 4096843093898110098663714001045428496102) * 10^40
        + 4044749075904908413507516386371121096381) * 10^40
        + 6120690833054502382634915717873189474332) * 10^40
        + 173581108125394463996200747787619064740) * 10^40
        + 7978955560061440981790983834282902945792)))

noncomputable def batchN05119MinusP013Error2559 : ℝ := ((6400077247752853716294087521289 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN05119MinusP013BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP013Center2559‖ ≤ batchN05119MinusP013Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP013Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP013Input2559]
  have hs : compactExp2547 batchN05119MinusP013Input2559 5 =
      (batchN05119MinusP013Center2559, ((6400077247752853716294087521289 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP013Input2559 5).2 : ℝ) =
      batchN05119MinusP013Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP013Error2559]
  have h := compactExp_error2547 batchN05119MinusP013Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP013Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP013Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP013DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP013Factor2559 * embedPair2542 batchN05119MinusP013Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP013Factor2559 : ℝ) * batchN05119MinusP013Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP013Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP013Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP013BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP013Factor2559)

def batchN05119MinusP014Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((346671309892138695845011 : ℚ) /
        230584300921369395200000000))

def batchN05119MinusP014Center2559 : RatPair2542 := (((136690322917036379465415611784707965 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((6581292116332526340337433221276721 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP014Factor2559 : RatPair2542 := ((((((((((((((87429720868784427964245522490578
    *
    10^40
        + 5720188819406173730537369010832677371632) * 10^40
        + 9461326150663758114356466989764830591994) * 10^40
        + 4292054732553882703195786667827111894251) * 10^40
        + 2365994239747550544726844752046207688089) * 10^40
        + 9735942168172191085967246083867392389567) * 10^40
        + 3190829185283108196471302568462305810442) * 10^40
        + 323456275524102925074327336134374241917) * 10^40
        + 3247616192741611902306083372107103998970) * 10^40
        + 6656274194819406697079320165077863436801) * 10^40
        + 9730078469823032864680676928273304995605) * 10^40
        + 6716189483651080250124150611767590129921) : ℚ) /
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
    ((((((((((37161794767251823294 * 10^40
        + 2768733430228064848157380387804087745441) * 10^40
        + 2680698240428679192765559609745415366869) * 10^40
        + 5076850767778830725376696137686714371065) * 10^40
        + 3270187755867705858856946840526017982172) * 10^40
        + 5801269584564976897405993424114504659780) * 10^40
        + 9085084377737708745843689431059265444965) * 10^40
        + 8512084338526091896065946233293678381908) * 10^40
        + 422593096620971838824683537697468503323) : ℚ) /
        ((((((((691040494459698 * 10^40
        + 833571296138197312311186647363578238826) * 10^40
        + 8275142309204479722580401306792632154824) * 10^40
        + 6605827963164720709058475038059699146133) * 10^40
        + 4096843093898110098663714001045428496102) * 10^40
        + 4044749075904908413507516386371121096381) * 10^40
        + 6120690833054502382634915717873189474332) * 10^40
        + 173581108125394463996200747787619064740) * 10^40
        + 7978955560061440981790983834282902945792)))

noncomputable def batchN05119MinusP014Error2559 : ℝ := ((12871930907743310001781199682229 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119MinusP014BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP014Center2559‖ ≤ batchN05119MinusP014Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP014Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP014Input2559]
  have hs : compactExp2547 batchN05119MinusP014Input2559 5 =
      (batchN05119MinusP014Center2559, ((12871930907743310001781199682229 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP014Input2559 5).2 : ℝ) =
      batchN05119MinusP014Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP014Error2559]
  have h := compactExp_error2547 batchN05119MinusP014Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP014Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP014Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP014DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP014Factor2559 * embedPair2542 batchN05119MinusP014Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP014Factor2559 : ℝ) * batchN05119MinusP014Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP014Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP014Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP014BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP014Factor2559)

def batchN05119MinusP015Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((377408574479356852679047 : ℚ) /
        230584300921369395200000000))

def batchN05119MinusP015Center2559 : RatPair2542 := (((136661005905620481834759904936433059 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((7164303870450030101716770460711611 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP015Factor2559 : RatPair2542 :=
    ((((((((((((((103550258225061856762857274134788 *
    10^40
        + 335051153712995591762194499200531879050) * 10^40
        + 2742390558706036194931128019822407075985) * 10^40
        + 4525409384878838329164160897500957291236) * 10^40
        + 1404234491672202903188725577401354334476) * 10^40
        + 4709713346176118617566905190500987659051) * 10^40
        + 8489894624317268163890435155694771111546) * 10^40
        + 241879884221035083053601474589324620618) * 10^40
        + 9851279519509945141024976541354799730057) * 10^40
        + 7837737417815446425677333912385725320858) * 10^40
        + 5343018963408020278248191373920845768285) * 10^40
        + 4415766305706208515088666963460623868553) : ℚ) /
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
    ((((((((((47854425852773956142 * 10^40
        + 4075375435782044809499326054030024175378) * 10^40
        + 3934111356337334717150904087444211307408) * 10^40
        + 7024563165451837605299468992862529230934) * 10^40
        + 2622568614265822869645529834023330417727) * 10^40
        + 9779529014864830196745220083293704490332) * 10^40
        + 3931354983665979581921453150550742464600) * 10^40
        + 9204763466288387378810060430643429624474) * 10^40
        + 1303894751754619535581595318728884349927) : ℚ) /
        ((((((((691040494459698 * 10^40
        + 833571296138197312311186647363578238826) * 10^40
        + 8275142309204479722580401306792632154824) * 10^40
        + 6605827963164720709058475038059699146133) * 10^40
        + 4096843093898110098663714001045428496102) * 10^40
        + 4044749075904908413507516386371121096381) * 10^40
        + 6120690833054502382634915717873189474332) * 10^40
        + 173581108125394463996200747787619064740) * 10^40
        + 7978955560061440981790983834282902945792)))

noncomputable def batchN05119MinusP015Error2559 : ℝ := ((403857064041269846621405252083 : ℝ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))

theorem batchN05119MinusP015BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP015Center2559‖ ≤ batchN05119MinusP015Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP015Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP015Input2559]
  have hs : compactExp2547 batchN05119MinusP015Input2559 5 =
      (batchN05119MinusP015Center2559, ((403857064041269846621405252083 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP015Input2559 5).2 : ℝ) =
      batchN05119MinusP015Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP015Error2559]
  have h := compactExp_error2547 batchN05119MinusP015Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP015Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP015Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP015DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP015Factor2559 * embedPair2542 batchN05119MinusP015Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP015Factor2559 : ℝ) * batchN05119MinusP015Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP015Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP015Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP015BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP015Factor2559)

def batchN05119MinusP016Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((199810861117846303095609 : ℚ) /
        115292150460684697600000000))

def batchN05119MinusP016Center2559 : RatPair2542 := (((136638271243340928355018544145654227 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((1896388289541678470197733149321781 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN05119MinusP016Factor2559 : RatPair2542 := ((((((((((((((29013038500985733045873458099125
    *
    10^40
        + 5309153040726766698992207931451529840853) * 10^40
        + 1179415526929222440160634147763738026517) * 10^40
        + 9762763470930013156139710841435065742118) * 10^40
        + 9120953984060071899272141783989174640600) * 10^40
        + 2272831540680543462667216667376958965179) * 10^40
        + 8324075518150438875865746188806366000631) * 10^40
        + 1038308128846694969359893360470139227001) * 10^40
        + 656989274498192744152786804539751981719) * 10^40
        + 6294462173114428413101342559160130711864) * 10^40
        + 6718482790426052651275477251625095440787) * 10^40
        + 5803739204325158021816111832935502373897) : ℚ) /
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
    ((((((((((7093223455333613687 * 10^40
        + 823910422818388463024274882529264004889) * 10^40
        + 812310078216665756098328525954808438990) * 10^40
        + 6312843206757210881044737395296752344822) * 10^40
        + 1439082464225097595389089163815807485012) * 10^40
        + 3247058496229778338353894174667576193389) * 10^40
        + 4722157781605587811943521288048428133749) * 10^40
        + 7289916644670959301290022442018259872150) * 10^40
        + 7461869286630545480504048711329631335001) : ℚ) /
        ((((((((86380061807462 * 10^40
        + 2604196412017274664038898330920447279853) * 10^40
        + 3534392788650559965322550163349079019353) * 10^40
        + 825728495395590088632309379757462393266) * 10^40
        + 6762105386737263762332964250130678562012) * 10^40
        + 8005593634488113551688439548296390137047) * 10^40
        + 7015086354131812797829364464734148684291) * 10^40
        + 5021697638515674307999525093473452383092) * 10^40
        + 5997369445007680122723872979285362868224)))

noncomputable def batchN05119MinusP016Error2559 : ℝ := ((12960675035634320448554100562401 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119MinusP016BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP016Center2559‖ ≤ batchN05119MinusP016Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP016Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP016Input2559]
  have hs : compactExp2547 batchN05119MinusP016Input2559 5 =
      (batchN05119MinusP016Center2559, ((12960675035634320448554100562401 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP016Input2559 5).2 : ℝ) =
      batchN05119MinusP016Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP016Error2559]
  have h := compactExp_error2547 batchN05119MinusP016Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP016Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP016Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP016DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP016Factor2559 * embedPair2542 batchN05119MinusP016Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP016Factor2559 : ℝ) * batchN05119MinusP016Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP016Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP016Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP016BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP016Factor2559)

def batchN05119MinusP017Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((442769373018475956606027 : ℚ) /
        230584300921369395200000000))

def batchN05119MinusP017Center2559 : RatPair2542 := (((8536900004882588456406383771233277 : ℚ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)),
    ((2100898492058081899089742025959593 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN05119MinusP017Factor2559 : RatPair2542 :=
    ((((((((((((((142378994286214673217692492671709 *
    10^40
        + 3285595591659262351330043301093672589552) * 10^40
        + 4195621098045954948039257627193915990549) * 10^40
        + 7671812961066032894303769342196347232776) * 10^40
        + 8325587324421766213207457905640745233531) * 10^40
        + 628291871874000076686316246389717365317) * 10^40
        + 1499087389049705111888484323420082978062) * 10^40
        + 4672541308234214021494795226180501978758) * 10^40
        + 3911206703069139530322742406138979601629) * 10^40
        + 7580408854925879027615735785812383997861) * 10^40
        + 316933143529549175732028076448149500117) * 10^40
        + 1546810021203693341579025130221141410833) : ℚ) /
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
    ((((((((((11006626557582784259 * 10^40
        + 4550920865484362519672585880262848617737) * 10^40
        + 97918341550965457965837031477279986435) * 10^40
        + 6211715280205151628403284061667916485001) * 10^40
        + 6848250004802056911378752616263734309934) * 10^40
        + 3375689508057645370486929224632122047189) * 10^40
        + 8162366060677632904429126820833180374155) * 10^40
        + 6926014481103987221769029834981618443168) * 10^40
        + 2996421430088041255262998585564296712421) : ℚ) /
        ((((((((98720070637099 * 10^40
        + 7261938756591171044615883806766225462689) * 10^40
        + 5467877472743497103225771615256090307832) * 10^40
        + 943689709023531529865496434008528449447) * 10^40
        + 6299549013414015728380530571577918356586) * 10^40
        + 577821296557844059072502340910160156625) * 10^40
        + 9445812976150643197519273673981884210618) * 10^40
        + 8596225872589342066285171535398231294962) * 10^40
        + 9711279365723062997398711976326128992256)))

noncomputable def batchN05119MinusP017Error2559 : ℝ := ((13033111058234186885931559623125 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119MinusP017BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP017Center2559‖ ≤ batchN05119MinusP017Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP017Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP017Input2559]
  have hs : compactExp2547 batchN05119MinusP017Input2559 5 =
      (batchN05119MinusP017Center2559, ((13033111058234186885931559623125 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP017Input2559 5).2 : ℝ) =
      batchN05119MinusP017Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP017Error2559]
  have h := compactExp_error2547 batchN05119MinusP017Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP017Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP017Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP017DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP017Factor2559 * embedPair2542 batchN05119MinusP017Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP017Factor2559 : ℝ) * batchN05119MinusP017Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP017Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP017Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP017BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP017Factor2559)

def batchN05119MinusP018Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((114770645411675231749613 : ℚ) /
        57646075230342348800000000))

def batchN05119MinusP018Center2559 : RatPair2542 := (((68285512529954108971620731390025879 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((8712800879746020555240806347520833 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP018Factor2559 : RatPair2542 := ((((((((((((((9564699787959118555244168780892
    * 10^40
        + 7389934947634074706702636120002928243724) * 10^40
        + 2756757214798792963070893285783803649713) * 10^40
        + 2137862971979634577488524909659678083688) * 10^40
        + 297136896324292952261129903545031946882) * 10^40
        + 280085532721155560641544509357904954179) * 10^40
        + 9405337730140913249896029640032398151232) * 10^40
        + 5959431084472291711347686698781615451272) * 10^40
        + 5873412074339554909206777605487755403051) * 10^40
        + 6121953271006725518139072722893250598805) * 10^40
        + 699486023385318010844682170997467062200) * 10^40
        + 9731343756151335527057886319845471181313) : ℚ) /
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
    ((((((((((1341147576855107700 * 10^40
        + 5134624816404047243402150778381843349261) * 10^40
        + 6177250647991576882777609644614002074911) * 10^40
        + 2039077037984262929846925450339659094430) * 10^40
        + 1796590762508454643474081670226665941975) * 10^40
        + 658757357951711755989848807290022027177) * 10^40
        + 8239928881022937651042081424016988820500) * 10^40
        + 5301479933649709281798316491591382404695) * 10^40
        + 5133949039632980456586955936428943375973) : ℚ) /
        ((((((((10797507725932 * 10^40
        + 7825524551502159333004862291365055909981) * 10^40
        + 6691799098581319995665318770418634877419) * 10^40
        + 1353216061924448761079038672469682799158) * 10^40
        + 3345263173342157970291620531266334820251) * 10^40
        + 6000699204311014193961054943537048767130) * 10^40
        + 9626885794266476599728670558091768585536) * 10^40
        + 4377712204814459288499940636684181547886) * 10^40
        + 5749671180625960015340484122410670358528)))

noncomputable def batchN05119MinusP018Error2559 : ℝ := ((3265131410255233964747771445697 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN05119MinusP018BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP018Center2559‖ ≤ batchN05119MinusP018Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP018Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP018Input2559]
  have hs : compactExp2547 batchN05119MinusP018Input2559 5 =
      (batchN05119MinusP018Center2559, ((3265131410255233964747771445697 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP018Input2559 5).2 : ℝ) =
      batchN05119MinusP018Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP018Error2559]
  have h := compactExp_error2547 batchN05119MinusP018Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP018Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP018Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP018DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP018Factor2559 * embedPair2542 batchN05119MinusP018Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP018Factor2559 : ℝ) * batchN05119MinusP018Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP018Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP018Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP018BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP018Factor2559)

def batchN05119MinusP019Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((24428249467783476683391 : ℚ) /
        11529215046068469760000000))

def batchN05119MinusP019Center2559 : RatPair2542 := (((136534233555798974945647184761037397 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((2317876889724714927326394073006797 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN05119MinusP019Factor2559 : RatPair2542 := ((((((((((((((10829487492642627702142835282888
    *
    10^40
        + 9364806673256898338781872705440658839947) * 10^40
        + 8441502008338855751385136677082673872118) * 10^40
        + 5082025439892888338083992320184563685367) * 10^40
        + 1207304222596736174642742591827480642417) * 10^40
        + 4073581428458252656925040698276128623548) * 10^40
        + 7310010178084081184940339982022351550598) * 10^40
        + 1927877433796266708613222069614472362483) * 10^40
        + 7499077860408076102371378440874987248477) * 10^40
        + 8007583421194478408447608817316862263152) * 10^40
        + 7346256965703159640731290546374103375359) * 10^40
        + 2481127735211335765068066661670845467697) : ℚ) /
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
    ((((((((((1615115739825365076 * 10^40
        + 1332276699625961148391084568282700096796) * 10^40
        + 8517526303072661252052991110059768391231) * 10^40
        + 9236510472484891911416246386209805269632) * 10^40
        + 8711918752002368482278302842032392799869) * 10^40
        + 8284048418114502149817179504804342425138) * 10^40
        + 8506296249088485899113270311645508345033) * 10^40
        + 3798627132751378635779113435004044224352) * 10^40
        + 5919123013233268135902975016372473047635) : ℚ) /
        ((((((((10797507725932 * 10^40
        + 7825524551502159333004862291365055909981) * 10^40
        + 6691799098581319995665318770418634877419) * 10^40
        + 1353216061924448761079038672469682799158) * 10^40
        + 3345263173342157970291620531266334820251) * 10^40
        + 6000699204311014193961054943537048767130) * 10^40
        + 9626885794266476599728670558091768585536) * 10^40
        + 4377712204814459288499940636684181547886) * 10^40
        + 5749671180625960015340484122410670358528)))

noncomputable def batchN05119MinusP019Error2559 : ℝ := ((409690937536066655923181125097 : ℝ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))

theorem batchN05119MinusP019BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP019Center2559‖ ≤ batchN05119MinusP019Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP019Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP019Input2559]
  have hs : compactExp2547 batchN05119MinusP019Input2559 5 =
      (batchN05119MinusP019Center2559, ((409690937536066655923181125097 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP019Input2559 5).2 : ℝ) =
      batchN05119MinusP019Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP019Error2559]
  have h := compactExp_error2547 batchN05119MinusP019Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP019Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP019Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP019DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP019Factor2559 * embedPair2542 batchN05119MinusP019Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP019Factor2559 : ℝ) * batchN05119MinusP019Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP019Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP019Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP019BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP019Factor2559)

def batchN05119MinusP020Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((520624750538575899551419 : ℚ) /
        230584300921369395200000000))

def batchN05119MinusP020Center2559 : RatPair2542 := (((136491631671103869188831385599620871 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((9878879938732765665723439748539677 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP020Factor2559 : RatPair2542 :=
    ((((((((((((((196706582303500573357604170828119 *
    10^40
        + 6580195463773896718287757549153701711602) * 10^40
        + 705047670810465760433424862144815659385) * 10^40
        + 6860142781828838261379633507243131680544) * 10^40
        + 8346373085781418930114180333702320589793) * 10^40
        + 7275718227116669668661715091673353241082) * 10^40
        + 6444287608606057488131132530541686465718) * 10^40
        + 738426805116687597716917612201326614578) * 10^40
        + 4112356080543866649431846593734375630730) * 10^40
        + 3086542089413808767393477125719347103450) * 10^40
        + 9667077423386388043605410975900926847674) * 10^40
        + 1512953769696634963723524666592066460081) : ℚ) /
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
    ((((((((((17855080400674679791 * 10^40
        + 7644602844206682296222341852460843209067) * 10^40
        + 314913395186720107477020460294543798971) * 10^40
        + 6052452377490033280392573244739016426746) * 10^40
        + 8484086783987146773531209484322917361917) * 10^40
        + 2862473565442007302267536794265294300474) * 10^40
        + 3645077644111771196524099166080241777466) * 10^40
        + 6158276093506139510902127973369557637478) * 10^40
        + 6006531248511635332179130751125385645461) : ℚ) /
        ((((((((98720070637099 * 10^40
        + 7261938756591171044615883806766225462689) * 10^40
        + 5467877472743497103225771615256090307832) * 10^40
        + 943689709023531529865496434008528449447) * 10^40
        + 6299549013414015728380530571577918356586) * 10^40
        + 577821296557844059072502340910160156625) * 10^40
        + 9445812976150643197519273673981884210618) * 10^40
        + 8596225872589342066285171535398231294962) * 10^40
        + 9711279365723062997398711976326128992256)))

noncomputable def batchN05119MinusP020Error2559 : ℝ := ((13164085247522669006634164507403 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119MinusP020BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP020Center2559‖ ≤ batchN05119MinusP020Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP020Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP020Input2559]
  have hs : compactExp2547 batchN05119MinusP020Input2559 5 =
      (batchN05119MinusP020Center2559, ((13164085247522669006634164507403 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP020Input2559 5).2 : ℝ) =
      batchN05119MinusP020Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP020Error2559]
  have h := compactExp_error2547 batchN05119MinusP020Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP020Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP020Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP020DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP020Factor2559 * embedPair2542 batchN05119MinusP020Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP020Factor2559 : ℝ) * batchN05119MinusP020Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP020Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP020Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP020BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP020Factor2559)

def batchN05119MinusP021Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((547379874475946380671387 : ℚ) /
        230584300921369395200000000))

def batchN05119MinusP021Center2559 : RatPair2542 := (((136454010412523374539035245978191931 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((10385606743139467390058717359548691 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP021Factor2559 : RatPair2542 :=
    ((((((((((((((217403606945932734613561011347158 *
    10^40
        + 8478872514566486261960423317123405799442) * 10^40
        + 7660503581984239377907331440276568636158) * 10^40
        + 6635252575170131607239939521544974516853) * 10^40
        + 6626690810103676251250045682886779266594) * 10^40
        + 2220901959697805352913475332352393478010) * 10^40
        + 5345105498520335462908460754841768299297) * 10^40
        + 7719887235119317974908646789395113012670) * 10^40
        + 8938075309157487107848270743764966441000) * 10^40
        + 5684950003938936838283935286044127390150) * 10^40
        + 2773151122874725353957707235297653785898) * 10^40
        + 7595728543044955274729072594971460849393) : ℚ) /
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
    ((((((((((145183991647549235013 * 10^40
        + 3919556466399027459499650573337799028325) * 10^40
        + 3711606587033261058661889848600265785679) * 10^40
        + 7850765372746381852878182557221095913742) * 10^40
        + 9523898911963823756081133414368209592674) * 10^40
        + 3901572953862229358288372426961909229817) * 10^40
        + 5229718525510229144975758247474465685017) * 10^40
        + 7954843058561600606163382846046815826210) * 10^40
        + 3191112406065884794623455720311086583987) : ℚ) /
        ((((((((691040494459698 * 10^40
        + 833571296138197312311186647363578238826) * 10^40
        + 8275142309204479722580401306792632154824) * 10^40
        + 6605827963164720709058475038059699146133) * 10^40
        + 4096843093898110098663714001045428496102) * 10^40
        + 4044749075904908413507516386371121096381) * 10^40
        + 6120690833054502382634915717873189474332) * 10^40
        + 173581108125394463996200747787619064740) * 10^40
        + 7978955560061440981790983834282902945792)))

noncomputable def batchN05119MinusP021Error2559 : ℝ := ((6604587085869879578309401578647 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN05119MinusP021BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP021Center2559‖ ≤ batchN05119MinusP021Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP021Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP021Input2559]
  have hs : compactExp2547 batchN05119MinusP021Input2559 5 =
      (batchN05119MinusP021Center2559, ((6604587085869879578309401578647 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP021Input2559 5).2 : ℝ) =
      batchN05119MinusP021Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP021Error2559]
  have h := compactExp_error2547 batchN05119MinusP021Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP021Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP021Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP021DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP021Factor2559 * embedPair2542 batchN05119MinusP021Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP021Factor2559 : ℝ) * batchN05119MinusP021Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP021Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP021Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP021BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP021Factor2559)

def batchN05119MinusP022Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((112214826711468142236233 : ℚ) /
        46116860184273879040000000))

def batchN05119MinusP022Center2559 : RatPair2542 := (((34108506643302950808937543788515145 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((5322456625100786892942830619525167 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchN05119MinusP022Factor2559 : RatPair2542 :=
    ((((((((((((((228398323416296552823862627041887 *
    10^40
        + 4067408802143617226841217980652715036384) * 10^40
        + 2210787034695814972074398881729505394975) * 10^40
        + 1709731476441498332741022727800007345614) * 10^40
        + 8858136509657161754858046117250197070288) * 10^40
        + 9076551623072459375506370262419572222442) * 10^40
        + 5909857701116382792614614900719688907122) * 10^40
        + 4955369802774458838110184524451389212693) * 10^40
        + 3634674155783555621294333568118695638734) * 10^40
        + 3592340702774100773803750426619766319062) * 10^40
        + 3572033894810208413442725355722434127329) * 10^40
        + 2831715011917141981174188964675688632577) : ℚ) /
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
    ((((((((((156317035586163538070 * 10^40
        + 3389512394118192611217966632342605042203) * 10^40
        + 5408815353239030113441605270392408460810) * 10^40
        + 8972497633541292185780690173717704737377) * 10^40
        + 209050710894561977852499071124842402137) * 10^40
        + 2634400230405119437841026360368266710218) * 10^40
        + 9647157086584601941391407991509850368378) * 10^40
        + 8327306193682533674031414822919264551607) * 10^40
        + 3349373624051493156884491757706821823205) : ℚ) /
        ((((((((691040494459698 * 10^40
        + 833571296138197312311186647363578238826) * 10^40
        + 8275142309204479722580401306792632154824) * 10^40
        + 6605827963164720709058475038059699146133) * 10^40
        + 4096843093898110098663714001045428496102) * 10^40
        + 4044749075904908413507516386371121096381) * 10^40
        + 6120690833054502382634915717873189474332) * 10^40
        + 173581108125394463996200747787619064740) * 10^40
        + 7978955560061440981790983834282902945792)))

noncomputable def batchN05119MinusP022Error2559 : ℝ := ((13232267893962419016699072549841 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119MinusP022BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP022Center2559‖ ≤ batchN05119MinusP022Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP022Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP022Input2559]
  have hs : compactExp2547 batchN05119MinusP022Input2559 5 =
      (batchN05119MinusP022Center2559, ((13232267893962419016699072549841 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP022Input2559 5).2 : ℝ) =
      batchN05119MinusP022Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP022Error2559]
  have h := compactExp_error2547 batchN05119MinusP022Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP022Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP022Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP022DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP022Factor2559 * embedPair2542 batchN05119MinusP022Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP022Factor2559 : ℝ) * batchN05119MinusP022Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP022Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP022Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP022BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP022Factor2559)

def batchN05119MinusP023Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((300278613592663314364333 : ℚ) /
        115292150460684697600000000))

def batchN05119MinusP023Center2559 : RatPair2542 := (((136373651225292125419020342027441741 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((11392323580664353380926712831803879 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP023Factor2559 : RatPair2542 := ((((((((((((((65404727912208469640274515938354
    *
    10^40
        + 6970328774684770458543206684977929119119) * 10^40
        + 1499446799415151900185492289807473079802) * 10^40
        + 8172526955181220176422968924465139682080) * 10^40
        + 2880151934691670325580818423292351244006) * 10^40
        + 2461028668006649886056909983254541121315) * 10^40
        + 7358845221387491275176987692776904489374) * 10^40
        + 1185955700318128260242820019582984211539) * 10^40
        + 532478573476188125888463291423113655871) * 10^40
        + 9309217188127475772887663972890791970529) * 10^40
        + 4373100622559405888491673262452339558370) * 10^40
        + 6504993759183225201696218662484675521409) : ℚ) /
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
    ((((((((((23946986057565093873 * 10^40
        + 3011129088504241205315858295621786152909) * 10^40
        + 6886012479830831298101977408583923657422) * 10^40
        + 9938794315470445623300711277056651113042) * 10^40
        + 4782802139250470569635256656875159610811) * 10^40
        + 9878455789814536378665391698566907081599) * 10^40
        + 1582847338299519666271288688692888110155) * 10^40
        + 9299284588900645641899586547154195406134) * 10^40
        + 4587258261920717909772745129720750428581) : ℚ) /
        ((((((((86380061807462 * 10^40
        + 2604196412017274664038898330920447279853) * 10^40
        + 3534392788650559965322550163349079019353) * 10^40
        + 825728495395590088632309379757462393266) * 10^40
        + 6762105386737263762332964250130678562012) * 10^40
        + 8005593634488113551688439548296390137047) * 10^40
        + 7015086354131812797829364464734148684291) * 10^40
        + 5021697638515674307999525093473452383092) * 10^40
        + 5997369445007680122723872979285362868224)))

noncomputable def batchN05119MinusP023Error2559 : ℝ := ((13298909874679709891445635516237 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119MinusP023BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP023Center2559‖ ≤ batchN05119MinusP023Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP023Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP023Input2559]
  have hs : compactExp2547 batchN05119MinusP023Input2559 5 =
      (batchN05119MinusP023Center2559, ((13298909874679709891445635516237 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP023Input2559 5).2 : ℝ) =
      batchN05119MinusP023Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP023Error2559]
  have h := compactExp_error2547 batchN05119MinusP023Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP023Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP023Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP023DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP023Factor2559 * embedPair2542 batchN05119MinusP023Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP023Factor2559 : ℝ) * batchN05119MinusP023Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP023Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP023Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP023BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP023Factor2559)

def batchN05119MinusP024Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((309351029057948556428147 : ℚ) /
        115292150460684697600000000))

def batchN05119MinusP024Center2559 : RatPair2542 := (((68172265935803253145831594145190809 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((5867844872622722568474542792324631 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchN05119MinusP024Factor2559 : RatPair2542 := ((((((((((((((69410782127648743995335396792350
    *
    10^40
        + 8115641433439150787160165830988335956142) * 10^40
        + 9702979331788613656488100193568193888411) * 10^40
        + 2940997913994613456666332116455906947238) * 10^40
        + 5642516585361224295078401472117843710704) * 10^40
        + 6197977296598866809090572473731680091174) * 10^40
        + 9689705038495486034640890639152157996362) * 10^40
        + 140737542847452480189417458577877400251) * 10^40
        + 311536701717655333885510377347606053771) * 10^40
        + 5845640067940695078709224643213609159653) * 10^40
        + 8087374645948541448708696565187522788087) * 10^40
        + 2720859513623690962527200212974320359489) : ℚ) /
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
    ((((((((((26177370953533623756 * 10^40
        + 193992744294576560373524758700076785496) * 10^40
        + 9766915951823765347714635782195131264594) * 10^40
        + 6446565648971011511484750751002675411770) * 10^40
        + 7505374685366708005677375589238192982006) * 10^40
        + 2580116713336272700661557730036837071630) * 10^40
        + 4078214333073623311076199998447843201256) * 10^40
        + 6141455316636953656248712284352338758022) * 10^40
        + 9798275179090484192262855101498647391419) : ℚ) /
        ((((((((86380061807462 * 10^40
        + 2604196412017274664038898330920447279853) * 10^40
        + 3534392788650559965322550163349079019353) * 10^40
        + 825728495395590088632309379757462393266) * 10^40
        + 6762105386737263762332964250130678562012) * 10^40
        + 8005593634488113551688439548296390137047) * 10^40
        + 7015086354131812797829364464734148684291) * 10^40
        + 5021697638515674307999525093473452383092) * 10^40
        + 5997369445007680122723872979285362868224)))

noncomputable def batchN05119MinusP024Error2559 : ℝ := ((3332391190051878303674760602877 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN05119MinusP024BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP024Center2559‖ ≤ batchN05119MinusP024Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP024Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP024Input2559]
  have hs : compactExp2547 batchN05119MinusP024Input2559 5 =
      (batchN05119MinusP024Center2559, ((3332391190051878303674760602877 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP024Input2559 5).2 : ℝ) =
      batchN05119MinusP024Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP024Error2559]
  have h := compactExp_error2547 batchN05119MinusP024Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP024Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP024Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP024DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP024Factor2559 * embedPair2542 batchN05119MinusP024Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP024Factor2559 : ℝ) * batchN05119MinusP024Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP024Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP024Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP024BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP024Factor2559)

def batchN05119MinusP025Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((10022692915539018190833 : ℚ) /
        3602879701896396800000000))

def batchN05119MinusP025Center2559 : RatPair2542 := (((8519175001980677903851323210829031 : ℚ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)),
    ((12166102506753169410234910000014849 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP025Factor2559 : RatPair2542 := ((((((((((((((72853623465835305318761199292 *
    10^40
        + 5164468449578975301421824568889658373085) * 10^40
        + 3811036814994898240278504289462540212360) * 10^40
        + 7042773171888787471032888996908919198673) * 10^40
        + 207636252012172176568874680077164950150) * 10^40
        + 7759443825003827953054795368753194061623) * 10^40
        + 7997227669231505607927560429163751094) * 10^40
        + 1666922527928445089727918038450094009342) * 10^40
        + 1444039340450837797839660951857557153942) * 10^40
        + 6030910546598125816047389658874395140525) * 10^40
        + 6496563366860899519486701604373954224195) * 10^40
        + 1886090822521410444885062374241653877433) : ℚ) /
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
    ((((((((((18163842211671 * 10^40
        + 4336429658187507583470991265828389914171) * 10^40
        + 9291144415906625006151607909592975107730) * 10^40
        + 2461156324118519345200598602108176043106) * 10^40
        + 720816953790513939381172923511310458659) * 10^40
        + 7902227140917101188025189570334222960263) * 10^40
        + 5580152706743959764445938568968151308043) * 10^40
        + 4708216630575508016587751746216390267872) * 10^40
        + 6740378665992038905018659821728236706577) : ℚ) /
        ((((((((53798169 * 10^40
        + 745215967417448093507518558983833730548) * 10^40
        + 208748663699271471021980953637049678306) * 10^40
        + 7473450221301328944359659394126038692217) * 10^40
        + 3905768421472284270158892157707525840714) * 10^40
        + 7852140469044983214157136684146521928057) * 10^40
        + 747516875028869711000277665968581053534) * 10^40
        + 4862904464844770480206116967975908223959) * 10^40
        + 4023366498281950663464681025211866284032)))

noncomputable def batchN05119MinusP025Error2559 : ℝ := ((13368025902742731320677342707611 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119MinusP025BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP025Center2559‖ ≤ batchN05119MinusP025Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP025Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP025Input2559]
  have hs : compactExp2547 batchN05119MinusP025Input2559 5 =
      (batchN05119MinusP025Center2559, ((13368025902742731320677342707611 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP025Input2559 5).2 : ℝ) =
      batchN05119MinusP025Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP025Error2559]
  have h := compactExp_error2547 batchN05119MinusP025Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP025Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP025Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP025DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP025Factor2559 * embedPair2542 batchN05119MinusP025Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP025Factor2559 : ℝ) * batchN05119MinusP025Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP025Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP025Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP025BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP025Factor2559)

def batchN05119MinusP026Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((20771944281655350607437 : ℚ) /
        7205759403792793600000000))

def batchN05119MinusP026Center2559 : RatPair2542 := (((34066708954997666427244722471119259 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((12605841530492533156490411532062923 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP026Factor2559 : RatPair2542 := ((((((((((((((312894923742656155747510336133 *
    10^40
        + 3522500999497512155699213583013203535040) * 10^40
        + 873701619072752867651962972385147826342) * 10^40
        + 4083607536606915540824824017115117633074) * 10^40
        + 6139814991509693842711720548039109929029) * 10^40
        + 3728891937059776861864290175371754353038) * 10^40
        + 5607055220190597329708118768949971596461) * 10^40
        + 7095958662183297671176238192249906029437) * 10^40
        + 7831214342623271540526617314967578429233) * 10^40
        + 5143610628306712307904067485187759637011) * 10^40
        + 3618183904532554163802896804973632230826) * 10^40
        + 6119368852043227056962074150298184612289) : ℚ) /
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
    ((((((((((7920837066027622 * 10^40
        + 3566809347016274608457323336524895613540) * 10^40
        + 9603567252262418161546400680353175661328) * 10^40
        + 8258064310281349212525739218628679955167) * 10^40
        + 9909040836621463001586675910891055388534) * 10^40
        + 7644261211510525155454142163411091407362) * 10^40
        + 64914200297921295894418507462691054117) * 10^40
        + 9048349855295145861042028627984356336808) * 10^40
        + 9568759025325437305483559656948118611589) : ℚ) /
        ((((((((21088882277 * 10^40
        + 2124659227639652654947275121662822374824) * 10^40
        + 1829476170114416640616533825723473896244) * 10^40
        + 9592486750120946188986482497407167349217) * 10^40
        + 1061221217135433902285725821350129560195) * 10^40
        + 8039063865633419949597580185436595798373) * 10^40
        + 3026615011316926712108845059683772985518) * 10^40
        + 6258550219150028240797851446556023792085) * 10^40
        + 7159667326524660078154961883051583340544)))

noncomputable def batchN05119MinusP026Error2559 : ℝ := ((3351840201121234744157453580137 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN05119MinusP026BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP026Center2559‖ ≤ batchN05119MinusP026Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP026Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP026Input2559]
  have hs : compactExp2547 batchN05119MinusP026Input2559 5 =
      (batchN05119MinusP026Center2559, ((3351840201121234744157453580137 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP026Input2559 5).2 : ℝ) =
      batchN05119MinusP026Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP026Error2559]
  have h := compactExp_error2547 batchN05119MinusP026Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP026Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP026Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP026DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP026Factor2559 * embedPair2542 batchN05119MinusP026Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP026Factor2559 : ℝ) * batchN05119MinusP026Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP026Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP026Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP026BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP026Factor2559)

def batchN05119MinusP027Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((43640783619197408678627 : ℚ) /
        14411518807585587200000000))

def batchN05119MinusP027Center2559 : RatPair2542 := (((68103332828402352451152359566069131 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((6620083378243797487725404228405657 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchN05119MinusP027Factor2559 : RatPair2542 := ((((((((((((((1380959343910727225099085892533
    * 10^40
        + 4545482060870658291723994712626150273175) * 10^40
        + 3729374178106333993492254113665851875998) * 10^40
        + 6915894089512825900402410277703582216410) * 10^40
        + 9444119085991083274368929739737985384371) * 10^40
        + 1991257198873376701923235337241655520844) * 10^40
        + 809896202464833368110585270504042860884) * 10^40
        + 1157856668210288391113546481591404784049) * 10^40
        + 1693477054691974067986388467134037411712) * 10^40
        + 5758371985537016491834038667828210502723) * 10^40
        + 6144331927412377527050208066191863083560) * 10^40
        + 6993469936937485015156074497651070965473) : ℚ) /
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
    ((((((((((73430467093451248 * 10^40
        + 5982446137321375747170549116275567499048) * 10^40
        + 9485608831103774469384835723225682380775) * 10^40
        + 4278152863697734148442090838512410862450) * 10^40
        + 2293723535378204035345142406622932706939) * 10^40
        + 8394855188044601150186773402792715445472) * 10^40
        + 6578439921436707783043709115234027972240) * 10^40
        + 8308608958598841808251476953562459844863) * 10^40
        + 5003469629845156743757640369427422188427) : ℚ) /
        ((((((((168711058217 * 10^40
        + 6997273821117221239578200973302578998593) * 10^40
        + 4635809360915333124932270605787791169959) * 10^40
        + 6739894000967569511891859979257338793736) * 10^40
        + 8489769737083471218285806570801036481566) * 10^40
        + 4312510925067359596780641483492766386986) * 10^40
        + 4212920090535413696870760477470183884149) * 10^40
        + 68401753200225926382811572448190336685) * 10^40
        + 7277338612197280625239695064412666724352)))

noncomputable def batchN05119MinusP027Error2559 : ℝ := ((841510870720748436607015000339 : ℝ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))

theorem batchN05119MinusP027BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP027Center2559‖ ≤ batchN05119MinusP027Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP027Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP027Input2559]
  have hs : compactExp2547 batchN05119MinusP027Input2559 5 =
      (batchN05119MinusP027Center2559, ((841510870720748436607015000339 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP027Input2559 5).2 : ℝ) =
      batchN05119MinusP027Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP027Error2559]
  have h := compactExp_error2547 batchN05119MinusP027Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP027Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP027Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP027DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP027Factor2559 * embedPair2542 batchN05119MinusP027Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP027Factor2559 : ℝ) * batchN05119MinusP027Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP027Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP027Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP027BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP027Factor2559)

def batchN05119MinusP028Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((177883892884016178388727 : ℚ) /
        57646075230342348800000000))

def batchN05119MinusP028Center2559 : RatPair2542 := (((136182027442187757030512704326884739 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((13491226290423052758738845485893577 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP028Factor2559 : RatPair2542 := ((((((((((((((22943082228526802907381804333802
    *
    10^40
        + 3390586134028304358823603231939609566910) * 10^40
        + 4683258957342854157658271679001839907004) * 10^40
        + 9976468380695015185302423254072392937026) * 10^40
        + 5656325440910670231771494275531885129797) * 10^40
        + 3346030779692399427232939955872915125576) * 10^40
        + 4569689981951630489766730255925261697954) * 10^40
        + 7819827599273757371392955629052436966374) * 10^40
        + 9013280111030013803266942715885551898727) * 10^40
        + 4412992927850406581386247717687242942217) * 10^40
        + 9567852997559920839827882446358897742988) * 10^40
        + 3963276993414647786632574739740794294953) : ℚ) /
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
    ((((((((((452028139897348047 * 10^40
        + 3366787830869052528275410924171480199979) * 10^40
        + 815359582120008084618445571343598236561) * 10^40
        + 755364673952654316695101150254211632519) * 10^40
        + 5663971488111229828738771692990700274556) * 10^40
        + 9448327930569489710809771169497704998006) * 10^40
        + 5036530781198680445824645403237970767333) * 10^40
        + 9755124339031614648659707510616789501403) * 10^40
        + 9065120487522422036070412271666508742917) : ℚ) /
        ((((((((981591611448 * 10^40
        + 4347774959227469030273169299215005082725) * 10^40
        + 6062890827143756363242301706401694079765) * 10^40
        + 3759383278356768069189003515679062072650) * 10^40
        + 7576842106667468906390147321024212256386) * 10^40
        + 5090972654937364926723732267594277160648) * 10^40
        + 2693353254024225145429879141644706235048) * 10^40
        + 7670701109528587208045449148789471049807) * 10^40
        + 8704515561875087274121862192946424578048)))

noncomputable def batchN05119MinusP028Error2559 : ℝ := ((6743341875678270580910058172461 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN05119MinusP028BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP028Center2559‖ ≤ batchN05119MinusP028Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP028Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP028Input2559]
  have hs : compactExp2547 batchN05119MinusP028Input2559 5 =
      (batchN05119MinusP028Center2559, ((6743341875678270580910058172461 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP028Input2559 5).2 : ℝ) =
      batchN05119MinusP028Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP028Error2559]
  have h := compactExp_error2547 batchN05119MinusP028Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP028Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP028Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP028DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP028Factor2559 * embedPair2542 batchN05119MinusP028Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP028Factor2559 : ℝ) * batchN05119MinusP028Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP028Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP028Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP028BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP028Factor2559)

def batchN05119MinusP029Input2559 : RatPair2542 := ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((411167 * 10^40
        + 1997436291662902877566187516556440623089) * 10^40
        + 4715741912281912185159794907545600000000)),
    ((182939534351242879487659 : ℚ) /
        57646075230342348800000000))

def batchN05119MinusP029Center2559 : RatPair2542 := (((136143628816801889985754233686278607 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((13873359999547748622963575466777233 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN05119MinusP029Factor2559 : RatPair2542 := ((((((((((((((24264374244924941092453568325404
    *
    10^40
        + 5628637374438375176863902102927457526373) * 10^40
        + 1601142730254534366082192269573565518530) * 10^40
        + 8176025635010889346188060962253138164645) * 10^40
        + 8731079905011955260254315945749322447023) * 10^40
        + 8389566983005102294324063006197130891823) * 10^40
        + 5222322237855261203408550584477296570269) * 10^40
        + 9888864166213389487077348766712139767636) * 10^40
        + 1872192787242643335560347013958598053933) * 10^40
        + 5114690509829178876141419623998039804362) * 10^40
        + 3185392735538112188847791868135939807439) * 10^40
        + 9926409004307597663886269270244269888081) : ℚ) /
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
    ((((((((((5407536625540063160 * 10^40
        + 1560838691931803669175970313743423025239) * 10^40
        + 4364805189645812830365212966899432720165) * 10^40
        + 6727956974607280408445409593873006871969) * 10^40
        + 6523044346896811404616372179796465611013) * 10^40
        + 5593416904296697376079852686015012090682) * 10^40
        + 1076422904238414429936751116413824740447) * 10^40
        + 7259429715309018963296555493019943553910) * 10^40
        + 7313150338641736159804291342583388241507) : ℚ) /
        ((((((((10797507725932 * 10^40
        + 7825524551502159333004862291365055909981) * 10^40
        + 6691799098581319995665318770418634877419) * 10^40
        + 1353216061924448761079038672469682799158) * 10^40
        + 3345263173342157970291620531266334820251) * 10^40
        + 6000699204311014193961054943537048767130) * 10^40
        + 9626885794266476599728670558091768585536) * 10^40
        + 4377712204814459288499940636684181547886) * 10^40
        + 5749671180625960015340484122410670358528)))

noncomputable def batchN05119MinusP029Error2559 : ℝ := ((13520971596804145523611194426485 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN05119MinusP029BaseError2559 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP029Center2559‖ ≤ batchN05119MinusP029Error2559 := by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hz : ‖embedPair2542 batchN05119MinusP029Input2559‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN05119MinusP029Input2559]
  have hs : compactExp2547 batchN05119MinusP029Input2559 5 =
      (batchN05119MinusP029Center2559, ((13520971596804145523611194426485 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN05119MinusP029Input2559 5).2 : ℝ) =
      batchN05119MinusP029Error2559 := by
    rw [hs]
    norm_num [batchN05119MinusP029Error2559]
  have h := compactExp_error2547 batchN05119MinusP029Input2559 hz 5
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      batchN05119MinusPosition2559 = Complex.exp ((2 : ℂ)^5 * embedPair2542
          batchN05119MinusP029Input2559) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN05119MinusPosition2559, storedWidth, nodeModulation2541,
      embedPair2542, batchN05119MinusP029Input2559, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN05119MinusP029DerivativeError2559 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN05119MinusPosition2559 -
      embedPair2542 batchN05119MinusP029Factor2559 * embedPair2542 batchN05119MinusP029Center2559‖
          ≤
        (pairMagnitude2542 batchN05119MinusP029Factor2559 : ℝ) * batchN05119MinusP029Error2559 :=
            by
  have hx : |batchN05119MinusPosition2559| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchN05119MinusPosition2559, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchN05119MinusPosition2559 = embedPair2542
          batchN05119MinusP029Factor2559 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN05119MinusPosition2559, storedWidth, nodeModulation2541, embedPair2542,
      batchN05119MinusP029Factor2559, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN05119MinusP029BaseError2559
    (embedPair_magnitude2542 batchN05119MinusP029Factor2559)

theorem batchN05119MinusGrid2559 :
    -stripRadius2303 + (5119 : ℝ) * (2 * stripRadius2303 / 10240) =
      batchN05119MinusPosition2559 := by
  norm_num [stripRadius2303, batchN05119MinusPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchN05119MinusP000DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP001DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP002DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP003DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP004DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP005DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP006DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP007DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP008DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP009DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP010DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP011DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP012DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP013DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP014DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP015DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP016DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP017DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP018DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP019DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP020DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP021DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP022DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP023DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP024DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP025DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP026DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP027DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP028DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusP029DerivativeError2559
#print axioms ConnesWeilRH.Dev.batchN05119MinusGrid2559
