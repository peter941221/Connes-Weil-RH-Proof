import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def neighborRightPosition2557 : ℝ := (((-79233025209) : ℝ) /
        25600000000)

theorem neighborRightZero2557 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def neighborRightP000Center2557 : RatPair2542 := (0, 0)

def neighborRightP000Factor2557 : RatPair2542 := (0, 0)

noncomputable def neighborRightP000Error2557 : ℝ := 0

theorem neighborRightP000Exterior2557 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩ neighborRightPosition2557 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |neighborRightPosition2557| := by
    norm_num [storedWidth, neighborRightPosition2557]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem neighborRightP000BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP000Center2557‖ ≤ neighborRightP000Error2557 := by
  rw [neighborRightP000Exterior2557]
  norm_num [neighborRightP000Center2557, neighborRightP000Error2557, neighborRightZero2557]

theorem neighborRightP000DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP000Factor2557 * embedPair2542 neighborRightP000Center2557‖ ≤
        (pairMagnitude2542 neighborRightP000Factor2557 : ℝ) * neighborRightP000Error2557 := by
  rw [neighborRightP000Exterior2557]
  norm_num [neighborRightP000Factor2557, neighborRightP000Center2557, neighborRightP000Error2557,
      neighborRightZero2557, pairMagnitude2542]

def neighborRightP001Input2557 : RatPair2542 := ((((-((18 * 10^40
        + 8957448532075589895690199699507613126779) * 10^40
        + 8635177651224989294368066657048977169169)) : ℚ) /
        ((52 * 10^40
        + 5327705452767415333723241392768703787170) * 10^40
        + 3821134574968135018370261083750400000000)),
    ((437706290102569059082793061 : ℚ) /
        1844674407370955161600000000))

def neighborRightP001Center2557 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def neighborRightP001Factor2557 : RatPair2542 := ((((((((((((((5302791 * 10^40
        + 9186757488946807771531041047867106470233) * 10^40
        + 2498672743913045202855460126088342475539) * 10^40
        + 1084635925602517214469513097198384833314) * 10^40
        + 2229126078306110986080108878221307507347) * 10^40
        + 5967188024830944801028069738657051784984) * 10^40
        + 7066512756312415329720654223577292254710) * 10^40
        + 3748747704431698714092879775318898764408) * 10^40
        + 9180244511914806857941447351101359279277) * 10^40
        + 3032291934954945963378264903979040791017) * 10^40
        + 850494405491281505119425157419212930232) * 10^40
        + 9516804556448181082825585529034382323093) : ℚ) /
        ((((((((((256561739412300154721745905821722014066 * 10^40
        + 2891801755297488142086282210811029025179) * 10^40
        + 5661661483804262145536189826030236453561) * 10^40
        + 4974671597761789718555418906186320968766) * 10^40
        + 8285758446500141270987646893778650093348) * 10^40
        + 4600579127089816697636832281422736988687) * 10^40
        + 6253883164626704029513108198706467546636) * 10^40
        + 6425113740564488976870856689727105519546) * 10^40
        + 7054560303152525233742881655739680438206) * 10^40
        + 4266154884070983969304014478239976063910) * 10^40
        + 7728444367415221537755694762772490354688)),
    (((-((((((((1886 * 10^40
        + 3790559012836049029217677204376030474898) * 10^40
        + 8157790270415996240130450083218527262268) * 10^40
        + 6092023366093854054434196452998400451406) * 10^40
        + 7743404178073321585719312151340880962003) * 10^40
        + 799777729297487402412450725230970614981) * 10^40
        + 8719218574484625652133550474122768473795) * 10^40
        + 7001672610031747428675116643548910751352) * 10^40
        + 3657324593805722690729771860715863871243)) : ℚ) /
        (((((((449563376228811642905470319697612153 * 10^40
        + 5266376055940757075056269020110826468215) * 10^40
        + 4397394730239828485440517685342776327934) * 10^40
        + 6320322075098826558105256491183187878265) * 10^40
        + 8645812069240071171828491750976455567098) * 10^40
        + 5307459993337195222934019647794257879545) * 10^40
        + 860122782819459623401760279013668619083) * 10^40
        + 5060256141902288286067943841365619638272)))

noncomputable def neighborRightP001Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP001BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP001Center2557‖ ≤ neighborRightP001Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP001Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP001Input2557]
  have hs : compactExp2547 neighborRightP001Input2557 9 =
      (neighborRightP001Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP001Input2557 9).2 : ℝ) = neighborRightP001Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP001Error2557]
  have h := compactExp_error2547 neighborRightP001Input2557 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          neighborRightP001Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP001Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP001DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP001Factor2557 * embedPair2542 neighborRightP001Center2557‖ ≤
        (pairMagnitude2542 neighborRightP001Factor2557 : ℝ) * neighborRightP001Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP001Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP001Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP001BaseError2557
    (embedPair_magnitude2542 neighborRightP001Factor2557)

def neighborRightP002Input2557 : RatPair2542 := ((((-((501 * 10^40
        + 8839822183730904454132100309844276595994) * 10^40
        + 5478704563309233690904404413326847597329)) : ℚ) /
        ((2039 * 10^40
        + 5757741460588060628394170300498186110020) * 10^40
        + 7730176828859850146962088670003200000000)),
    (((-437706290102569059082793061) : ℚ) /
        922337203685477580800000000))

def neighborRightP002Center2557 : RatPair2542 := ((((-327473819977610762985) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-137641572432642977529) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def neighborRightP002Factor2557 : RatPair2542 := ((((-(((((((((((723325957067660 * 10^40
        + 1571380707143384099370739835310195395625) * 10^40
        + 9826365953358443246297454824879435908649) * 10^40
        + 6997165609653651894626641198830951038656) * 10^40
        + 8280614743002061002801003628514452036393) * 10^40
        + 2995739446877183976227565818180719256261) * 10^40
        + 769901966468660869439827313650151051798) * 10^40
        + 7245712646042581208770913573345617015510) * 10^40
        + 8778449374813827535404682134235775884470) * 10^40
        + 1588844303289645089024021441260787905674) * 10^40
        + 4835822849244521463987532580435065757155) * 10^40
        + 1667324348788095758052568910712666247787)) : ℚ) /
        (((((((((((5623790053 * 10^40
        + 5345028717899208143525080632042257506957) * 10^40
        + 7996832095160324478376359060986242312243) * 10^40
        + 1809253644103034126971394547474786948468) * 10^40
        + 9554754557422551463909321429494115709931) * 10^40
        + 2286727896070595524025847268000335518199) * 10^40
        + 7478502534210252838492061593110828785940) * 10^40
        + 9334488126151931566759736467318051194990) * 10^40
        + 4187209450911610074049471336454739399112) * 10^40
        + 2346223783876610291901938608583906039912) * 10^40
        + 8905891477902200107998145960672855721424) * 10^40
        + 2397815274429841582277902829538517188608)),
    ((((((((((229190206 * 10^40
        + 6527933864630659188703855151047520408193) * 10^40
        + 348456529294173557495419090064829974127) * 10^40
        + 5167922829990196560200198334788722612951) * 10^40
        + 9380632817435141993970081077190743426569) * 10^40
        + 9567154845879064375923523721852494451242) * 10^40
        + 5520309926492190535611375927950680072430) * 10^40
        + 4988270927982764897147604700774165895078) * 10^40
        + 7046940838991128133386220819892507578123) : ℚ) /
        ((((((((1634 * 10^40
        + 3650356788179276370231281585653830944664) * 10^40
        + 9764650060649963238412078436451861610765) * 10^40
        + 5364633056375432662096857458669685019968) * 10^40
        + 4509381599398261992605584169384619994282) * 10^40
        + 6582824274867956171001273425255326607191) * 10^40
        + 7226395476136758207260259563595937505758) * 10^40
        + 389902966080521832726216138575373078980) * 10^40
        + 2695982315006962220652387737248613793792)))

noncomputable def neighborRightP002Error2557 : ℝ := ((2401498195160185481 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP002BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP002Center2557‖ ≤ neighborRightP002Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP002Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP002Input2557]
  have hs : compactExp2547 neighborRightP002Input2557 8 =
      (neighborRightP002Center2557, ((2401498195160185481 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP002Input2557 8).2 : ℝ) = neighborRightP002Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP002Error2557]
  have h := compactExp_error2547 neighborRightP002Input2557 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          neighborRightP002Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP002Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP002DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP002Factor2557 * embedPair2542 neighborRightP002Center2557‖ ≤
        (pairMagnitude2542 neighborRightP002Factor2557 : ℝ) * neighborRightP002Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP002Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP002Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP002BaseError2557
    (embedPair_magnitude2542 neighborRightP002Factor2557)

def neighborRightP003Input2557 : RatPair2542 := ((((-((10686 * 10^40
        + 5514579033133485558018445580747464399624) * 10^40
        + 6137789117471636006252046452959068041489)) : ℚ) /
        ((59001 * 10^40
        + 3089754565407751898622199770334889942512) * 10^40
        + 5741483004646831459175457370931200000000)),
    (((-437706290102569059082793061) : ℚ) /
        922337203685477580800000000))

def neighborRightP003Center2557 : RatPair2542 := ((((-170211882877148968493082023) : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    (((-2289353691360944363304748813) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def neighborRightP003Factor2557 : RatPair2542 := ((((-(((((((((((216836643179876819996239 * 10^40
        + 7003664316422113065538904154040780135093) * 10^40
        + 5317754813775061717731187929239645819342) * 10^40
        + 1831044618096853609807720081878962179142) * 10^40
        + 3005550364496348066792005527826778478478) * 10^40
        + 5234449206785679305025101812910020802036) * 10^40
        + 2183153901014248431018995756044195627920) * 10^40
        + 3019521868157618649502546970300704843552) * 10^40
        + 625800015567425553057062532614021956674) * 10^40
        + 5051913616494860507423211750352945671690) * 10^40
        + 9155753647207335234419137861611177781280) * 10^40
        + 7583437783831722572645350091496241282667)) : ℚ) /
        (((((((((((3295792879890984782 * 10^40
        + 7422290034568501577860678413768047342681) * 10^40
        + 6222898127092666488985088919772719587802) * 10^40
        + 5330384427348941392534046817921597146586) * 10^40
        + 3473835223814199285717056038623933304378) * 10^40
        + 1296437055164324127480266644871509541199) * 10^40
        + 2869835216847140093010829865258096304180) * 10^40
        + 2561072844919433666911073305524631745211) * 10^40
        + 4798279120988519142358006251065319202737) * 10^40
        + 9038208580419010027990736894021795130259) * 10^40
        + 7085557788088312432323047081833489422691) * 10^40
        + 6399582968343494245106392583552030998528)),
    (((-((((((((41522017008002 * 10^40
        + 1256236212345690459651497089872289603914) * 10^40
        + 2454530028932070961335615351731770320356) * 10^40
        + 9444504619017921015396607935444448240220) * 10^40
        + 1490426146453620675938671177808925333493) * 10^40
        + 4407040369506937715666805808928704189545) * 10^40
        + 8917651309217791369616324195048080447975) * 10^40
        + 9841153669119346041403682213936081355041) * 10^40
        + 1239404953046436600138603802602127665397)) : ℚ) /
        ((((((((1144553955 * 10^40
        + 7204356326498616829333140434645303712899) * 10^40
        + 8229299020552135100043796799444637263433) * 10^40
        + 3980010768663130427503160724229811498697) * 10^40
        + 1005038917578976128903718688904848957578) * 10^40
        + 4868745369166089736494351179175394281902) * 10^40
        + 9567999874501090188168737145900718068329) * 10^40
        + 7124158458887615287041127327241336151906) * 10^40
        + 7389616120338860115014967265567505907712)))

noncomputable def neighborRightP003Error2557 : ℝ := ((37431587606157667393148409 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP003BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP003Center2557‖ ≤ neighborRightP003Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP003Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP003Input2557]
  have hs : compactExp2547 neighborRightP003Input2557 8 =
      (neighborRightP003Center2557, ((37431587606157667393148409 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP003Input2557 8).2 : ℝ) = neighborRightP003Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP003Error2557]
  have h := compactExp_error2547 neighborRightP003Input2557 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          neighborRightP003Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP003Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP003DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP003Factor2557 * embedPair2542 neighborRightP003Center2557‖ ≤
        (pairMagnitude2542 neighborRightP003Factor2557 : ℝ) * neighborRightP003Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP003Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP003Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP003BaseError2557
    (embedPair_magnitude2542 neighborRightP003Factor2557)

def neighborRightP004Input2557 : RatPair2542 := ((((-((1168 * 10^40
        + 3530673673730106098996702978531164745704) * 10^40
        + 2277384033427170932559140326412785097329)) : ℚ) /
        ((7447 * 10^40
        + 8007525417628767465445011537519794516855) * 10^40
        + 5700019301591690146962088670003200000000)),
    ((437706290102569059082793061 : ℚ) /
        922337203685477580800000000))

def neighborRightP004Center2557 : RatPair2542 := ((((-676666070280422645745488920633) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((2275293504233894188352239524669 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def neighborRightP004Factor2557 : RatPair2542 := ((((-(((((((((((467723579224659681 * 10^40
        + 8484946496030013436548986532741950552835) * 10^40
        + 714889830005639318321580126512216137974) * 10^40
        + 7547578893524006678677434463007764219850) * 10^40
        + 1974501245739101126977392726558625719315) * 10^40
        + 2933074558244994895103664883854440541679) * 10^40
        + 7607347835003198443733637333182213096089) * 10^40
        + 5826080639562876526354994330146739902776) * 10^40
        + 1335602391487834594909747742014348838045) * 10^40
        + 2380140419226871435449990903967551102317) * 10^40
        + 8272307745980091482790805779660263400923) * 10^40
        + 6623657642667778265026770424384541247787)) : ℚ) /
        (((((((((((13333934833650 * 10^40
        + 9971517618121969154129984964871285267879) * 10^40
        + 5984738859495130611842348591889951463293) * 10^40
        + 6125164979236665047541932013894432763732) * 10^40
        + 5858167147305081960923219887441363572028) * 10^40
        + 8654616800009248802978886640846612251678) * 10^40
        + 1673769745154913406382432106665730699625) * 10^40
        + 5297790964096429504160747485828179300154) * 10^40
        + 3168687149004743606189981813750612831954) * 10^40
        + 6441012126335624117660080169510456621180) * 10^40
        + 9797768311222909063981655216539090444022) * 10^40
        + 3993060345224963310175502829538517188608)),
    ((((((((((15736248955 * 10^40
        + 5023204047840236269438247379236246939701) * 10^40
        + 7740563459287877372046636291461668116673) * 10^40
        + 2536045747219789253953330030130419607261) * 10^40
        + 6489456749410251819131789052928401229581) * 10^40
        + 234194580398171304314753494552592117232) * 10^40
        + 7241562934585527070699861045095106947769) * 10^40
        + 4199532113254545069587607087676226528366) * 10^40
        + 2615323203059540227583699004326242421877) : ℚ) /
        ((((((((290604 * 10^40
        + 1969094059240756694012022211275079450378) * 10^40
        + 5864164965006501410876788381978536002162) * 10^40
        + 2524647771234897950998468046614314353167) * 10^40
        + 4410927939648029517959407503537747456256) * 10^40
        + 4508596300616643358630491050424669059171) * 10^40
        + 88336592144474006884371272399339470295) * 10^40
        + 5153772248874244825826744633326275738853) * 10^40
        + 4815618956468741101573987737248613793792)))

noncomputable def neighborRightP004Error2557 : ℝ := ((9077586350185816146255924959 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem neighborRightP004BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP004Center2557‖ ≤ neighborRightP004Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP004Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP004Input2557]
  have hs : compactExp2547 neighborRightP004Input2557 8 =
      (neighborRightP004Center2557, ((9077586350185816146255924959 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP004Input2557 8).2 : ℝ) = neighborRightP004Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP004Error2557]
  have h := compactExp_error2547 neighborRightP004Input2557 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          neighborRightP004Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP004Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP004DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP004Factor2557 * embedPair2542 neighborRightP004Center2557‖ ≤
        (pairMagnitude2542 neighborRightP004Factor2557 : ℝ) * neighborRightP004Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP004Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP004Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP004BaseError2557
    (embedPair_magnitude2542 neighborRightP004Factor2557)

def neighborRightP005Center2557 : RatPair2542 := (0, 0)

def neighborRightP005Factor2557 : RatPair2542 := (0, 0)

noncomputable def neighborRightP005Error2557 : ℝ := 0

theorem neighborRightP005Exterior2557 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩ neighborRightPosition2557 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |neighborRightPosition2557| := by
    norm_num [storedWidth, neighborRightPosition2557]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem neighborRightP005BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP005Center2557‖ ≤ neighborRightP005Error2557 := by
  rw [neighborRightP005Exterior2557]
  norm_num [neighborRightP005Center2557, neighborRightP005Error2557, neighborRightZero2557]

theorem neighborRightP005DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP005Factor2557 * embedPair2542 neighborRightP005Center2557‖ ≤
        (pairMagnitude2542 neighborRightP005Factor2557 : ℝ) * neighborRightP005Error2557 := by
  rw [neighborRightP005Exterior2557]
  norm_num [neighborRightP005Factor2557, neighborRightP005Center2557, neighborRightP005Error2557,
      neighborRightZero2557, pairMagnitude2542]

def neighborRightP006Input2557 : RatPair2542 := ((((-16439531033496690691568499820795671) : ℚ) /
        27576812937084734710212198400000000),
    ((0 : ℚ) /
        1))

def neighborRightP006Center2557 : RatPair2542 := (((1061161581669737 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def neighborRightP006Factor2557 : RatPair2542 := ((((((15429265385220102 * 10^40
        + 4986090188441277973349836116988367194160) * 10^40
        + 2238199455504704556983830206440058913270) * 10^40
        + 948277081363794580136441120194187938081) : ℚ) /
        (((44409393516 * 10^40
        + 2023344271789931074110343813418828537211) * 10^40
        + 8005777342566079444652812457721294013794) * 10^40
        + 2485474144332436641091528961553503504648)),
    ((0 : ℚ) /
        1))

noncomputable def neighborRightP006Error2557 : ℝ := ((308762315073 : ℝ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))

theorem neighborRightP006BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP006Center2557‖ ≤ neighborRightP006Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP006Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP006Input2557]
  have hs : compactExp2547 neighborRightP006Input2557 7 =
      (neighborRightP006Center2557, ((308762315073 : ℚ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP006Input2557 7).2 : ℝ) = neighborRightP006Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP006Error2557]
  have h := compactExp_error2547 neighborRightP006Input2557 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          neighborRightP006Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP006Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP006DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP006Factor2557 * embedPair2542 neighborRightP006Center2557‖ ≤
        (pairMagnitude2542 neighborRightP006Factor2557 : ℝ) * neighborRightP006Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP006Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP006Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP006BaseError2557
    (embedPair_magnitude2542 neighborRightP006Factor2557)

def neighborRightP007Input2557 : RatPair2542 := ((((-((10686 * 10^40
        + 5514579033133485558018445580747464399624) * 10^40
        + 6137789117471636006252046452959068041489)) : ℚ) /
        ((14750 * 10^40
        + 3272438641351937974655549942583722485628) * 10^40
        + 1435370751161707864793864342732800000000)),
    ((0 : ℚ) /
        1))

def neighborRightP007Center2557 : RatPair2542 := (((5327421052927345222380711195 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def neighborRightP007Factor2557 : RatPair2542 := (((((((((((((17660011044724684545563072607381354
    *
    10^40
        + 589124938358210518771700543344343971266) * 10^40
        + 3743306743975635297476536767521327538117) * 10^40
        + 7016137101841820433310145458132300198561) * 10^40
        + 7394001739529456983557117133299235033852) * 10^40
        + 2478278598658322775703706465325720469094) * 10^40
        + 9428691398999092994011670458383258953931) * 10^40
        + 360824217427889836276192874715311224598) * 10^40
        + 4673001496130108902701947887370084552475) * 10^40
        + 6916044566084213949632420723592471081795) * 10^40
        + 5824706869972754152792422662511558077521) : ℚ) /
        ((((((((((6655800715908525290759910342022 * 10^40
        + 139238945924417499513781269295561511007) * 10^40
        + 2245835083371853791348998140693296409514) * 10^40
        + 1978055003605644344688352199494941965614) * 10^40
        + 2791811410015730749744434699609128096942) * 10^40
        + 1955299232985994784864562396469923993473) * 10^40
        + 5682875917107215182234841000647056524028) * 10^40
        + 3396699611110749051943610653269780799197) * 10^40
        + 6145500656374024861445456482697745573696) * 10^40
        + 1909813974424111658409947126889341277592) * 10^40
        + 9192982959782033222339381300092464620168)),
    ((0 : ℚ) /
        1))

noncomputable def neighborRightP007Error2557 : ℝ := ((1547288813920703326910549 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP007BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP007Center2557‖ ≤ neighborRightP007Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP007Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP007Input2557]
  have hs : compactExp2547 neighborRightP007Input2557 6 =
      (neighborRightP007Center2557, ((1547288813920703326910549 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP007Input2557 6).2 : ℝ) = neighborRightP007Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP007Error2557]
  have h := compactExp_error2547 neighborRightP007Input2557 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          neighborRightP007Input2557) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP007Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP007DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP007Factor2557 * embedPair2542 neighborRightP007Center2557‖ ≤
        (pairMagnitude2542 neighborRightP007Factor2557 : ℝ) * neighborRightP007Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP007Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP007Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP007BaseError2557
    (embedPair_magnitude2542 neighborRightP007Factor2557)

def neighborRightP008Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((315234250415438586120416073 : ℚ) /
        236118324143482260684800000000))

def neighborRightP008Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP008Factor2557 : RatPair2542 := ((((((((((((((32674261609590929245187691253208868
    *
    10^40
        + 8093665694690075392243379047256430085767) * 10^40
        + 587981623356345260339607763593922039110) * 10^40
        + 1924313966303305264339821501136069541624) * 10^40
        + 9669938420344915945665716801009137240535) * 10^40
        + 2199267944262325126146158118906593354825) * 10^40
        + 5118586597870980930983133151090958637412) * 10^40
        + 3434494425634887700048393324948695652047) * 10^40
        + 5765635666762775329234460860193561293184) * 10^40
        + 7767996815435157532786129281235516410567) * 10^40
        + 9517366369059349435490603326717700178276) * 10^40
        + 2784297821516540206290327078270960948157) : ℚ) /
        (((((((((((91704665452005 * 10^40
        + 2327825286843634285526529924068748047098) * 10^40
        + 5608156296906071094137519266680777218094) * 10^40
        + 1470852307582060063257283185535791747374) * 10^40
        + 3280623318771542527534902593663358567797) * 10^40
        + 1729025466241875725437757902980181814894) * 10^40
        + 8846867241640500435496506520058408685213) * 10^40
        + 3633205974727876818887423332684205948883) * 10^40
        + 4659436421371989984351307346578595860951) * 10^40
        + 9864387051676695467973755085747756216128) * 10^40
        + 1656468500290299954020915346649937734477) * 10^40
        + 5584645699454832454960289506110442831872)),
    (((-((((((((7111698388611080312030 * 10^40
        + 6215225384211360834490604247460394133137) * 10^40
        + 7747814358577072436059977181812800279640) * 10^40
        + 2050713718641492971303247320170824878654) * 10^40
        + 1739730446279896296362759295666529389338) * 10^40
        + 3537395601067787410533043732227645478511) * 10^40
        + 6537227467091722182957954560995258581097) * 10^40
        + 9489730879749040261677090714375384251800) * 10^40
        + 6939559728955179793657125180775598918671)) : ℚ) /
        ((((((((3336624 * 10^40
        + 558651103367555413902446549437994274060) * 10^40
        + 2595630609475083769512465552647335182650) * 10^40
        + 9915166904430167233788738472643902785721) * 10^40
        + 8590140480867267292263659679258013720057) * 10^40
        + 1903501574476612889314209692951789051109) * 10^40
        + 45179279704803950623035839446831364285) * 10^40
        + 7843080265014065323647915045963286532193) * 10^40
        + 9149762741836609099573600546157353762816)))

noncomputable def neighborRightP008Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP008BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP008Center2557‖ ≤ neighborRightP008Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP008Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP008Input2557]
  have hs : compactExp2547 neighborRightP008Input2557 15 =
      (neighborRightP008Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP008Input2557 15).2 : ℝ) = neighborRightP008Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP008Error2557]
  have h := compactExp_error2547 neighborRightP008Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP008Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP008Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP008DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP008Factor2557 * embedPair2542 neighborRightP008Center2557‖ ≤
        (pairMagnitude2542 neighborRightP008Factor2557 : ℝ) * neighborRightP008Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP008Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP008Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP008BaseError2557
    (embedPair_magnitude2542 neighborRightP008Factor2557)

def neighborRightP009Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((468835922968538293612120599 : ℚ) /
        236118324143482260684800000000))

def neighborRightP009Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP009Factor2557 : RatPair2542 := ((((((((((((((32674261609118622500105745097180954
    *
    10^40
        + 8299227735971610123249140898519984256098) * 10^40
        + 4213912911837768191821020774802509287947) * 10^40
        + 5567485165791132782890249598925930995975) * 10^40
        + 7816352058096050976314926099514749192841) * 10^40
        + 3805712340762570093210273743281571550530) * 10^40
        + 9895635780470462559861314440978700657970) * 10^40
        + 7733010084277198232154828773172739709944) * 10^40
        + 4334010859098129557034946145722195060293) * 10^40
        + 961995247230782985320972221055743274501) * 10^40
        + 2287092755951738018488899214852343875618) * 10^40
        + 2246600386910230418293336280961468634621) : ℚ) /
        (((((((((((91704665452005 * 10^40
        + 2327825286843634285526529924068748047098) * 10^40
        + 5608156296906071094137519266680777218094) * 10^40
        + 1470852307582060063257283185535791747374) * 10^40
        + 3280623318771542527534902593663358567797) * 10^40
        + 1729025466241875725437757902980181814894) * 10^40
        + 8846867241640500435496506520058408685213) * 10^40
        + 3633205974727876818887423332684205948883) * 10^40
        + 4659436421371989984351307346578595860951) * 10^40
        + 9864387051676695467973755085747756216128) * 10^40
        + 1656468500290299954020915346649937734477) * 10^40
        + 5584645699454832454960289506110442831872)),
    (((-((((((((10576958796510568255910 * 10^40
        + 3917284432989195709385370076609824310717) * 10^40
        + 58395010970674065985163937169796350080) * 10^40
        + 3707391589600509168340637460276412618327) * 10^40
        + 7469688203106015891460811131754198150917) * 10^40
        + 1803859774241136521022839170485346383698) * 10^40
        + 1760653845311769539342467884151533785002) * 10^40
        + 4543023675086448216786422873458658940019) * 10^40
        + 8115292953513722481457806380559057490641)) : ℚ) /
        ((((((((3336624 * 10^40
        + 558651103367555413902446549437994274060) * 10^40
        + 2595630609475083769512465552647335182650) * 10^40
        + 9915166904430167233788738472643902785721) * 10^40
        + 8590140480867267292263659679258013720057) * 10^40
        + 1903501574476612889314209692951789051109) * 10^40
        + 45179279704803950623035839446831364285) * 10^40
        + 7843080265014065323647915045963286532193) * 10^40
        + 9149762741836609099573600546157353762816)))

noncomputable def neighborRightP009Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP009BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP009Center2557‖ ≤ neighborRightP009Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP009Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP009Input2557]
  have hs : compactExp2547 neighborRightP009Input2557 15 =
      (neighborRightP009Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP009Input2557 15).2 : ℝ) = neighborRightP009Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP009Error2557]
  have h := compactExp_error2547 neighborRightP009Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP009Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP009Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP009DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP009Factor2557 * embedPair2542 neighborRightP009Center2557‖ ≤
        (pairMagnitude2542 neighborRightP009Factor2557 : ℝ) * neighborRightP009Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP009Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP009Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP009BaseError2557
    (embedPair_magnitude2542 neighborRightP009Factor2557)

def neighborRightP010Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((278897497562407945441511889 : ℚ) /
        118059162071741130342400000000))

def neighborRightP010Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP010Factor2557 : RatPair2542 := ((((((((((((((8168565402190115465775977217322679
    *
    10^40
        + 3292918996275165727856391692205586618725) * 10^40
        + 3332719569536891491098362505465035058999) * 10^40
        + 6865462335523804062894069411601711623869) * 10^40
        + 6578458081829057221880854068699188698035) * 10^40
        + 6155140487632713421887736339274177124866) * 10^40
        + 1335079871932135844748535077102501483148) * 10^40
        + 9170574588319733949328293110257081775517) * 10^40
        + 1596994640454414065569552784138995258406) * 10^40
        + 3781381397176191589162146297270643782943) * 10^40
        + 7470547251807827669336391842306498169852) * 10^40
        + 8655401076413013920614853174811444311373) : ℚ) /
        (((((((((((22926166363001 * 10^40
        + 3081956321710908571381632481017187011774) * 10^40
        + 6402039074226517773534379816670194304523) * 10^40
        + 5367713076895515015814320796383947936843) * 10^40
        + 5820155829692885631883725648415839641949) * 10^40
        + 2932256366560468931359439475745045453723) * 10^40
        + 7211716810410125108874126630014602171303) * 10^40
        + 3408301493681969204721855833171051487220) * 10^40
        + 8664859105342997496087826836644648965237) * 10^40
        + 9966096762919173866993438771436939054032) * 10^40
        + 414117125072574988505228836662484433619) * 10^40
        + 3896161424863708113740072376527610707968)),
    (((-((((((((1572984916282672851210 * 10^40
        + 9669073035442500363161967997313890820993) * 10^40
        + 8415278254838647957486861387931024058418) * 10^40
        + 3869810111352276511553696450387549833176) * 10^40
        + 4481895944827324412931157881624468181965) * 10^40
        + 9669870070155983737029188774915155090898) * 10^40
        + 3274291658237685979031939700269135138367) * 10^40
        + 2969145299403568808799079424869011545117) * 10^40
        + 1696368858916702288793572219986943594487)) : ℚ) /
        ((((((((417078 * 10^40
        + 69831387920944426737805818679749284257) * 10^40
        + 5324453826184385471189058194080916897831) * 10^40
        + 3739395863053770904223592309080487848215) * 10^40
        + 2323767560108408411532957459907251715007) * 10^40
        + 1487937696809576611164276211618973631388) * 10^40
        + 6255647409963100493827879479930853920535) * 10^40
        + 7230385033126758165455989380745410816524) * 10^40
        + 2393720342729576137446700068269669220352)))

noncomputable def neighborRightP010Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP010BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP010Center2557‖ ≤ neighborRightP010Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP010Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP010Input2557]
  have hs : compactExp2547 neighborRightP010Input2557 15 =
      (neighborRightP010Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP010Input2557 15).2 : ℝ) = neighborRightP010Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP010Error2557]
  have h := compactExp_error2547 neighborRightP010Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP010Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP010Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP010DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP010Factor2557 * embedPair2542 neighborRightP010Center2557‖ ≤
        (pairMagnitude2542 neighborRightP010Factor2557 : ℝ) * neighborRightP010Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP010Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP010Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP010BaseError2557
    (embedPair_magnitude2542 neighborRightP010Factor2557)

def neighborRightP011Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((308553336021908726764541409 : ℚ) /
        118059162071741130342400000000))

def neighborRightP011Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP011Factor2557 : RatPair2542 := ((((((((((((((8168565402121794341938507648149841
    *
    10^40
        + 6216393050103335511161158155446090693385) * 10^40
        + 3284474475765199094931348310916631574056) * 10^40
        + 3764261605998996128729411435392093264922) * 10^40
        + 4520552701024312185756458939152966954288) * 10^40
        + 1289747986226462849544370517154384552117) * 10^40
        + 2266921290347449338501153134291278844159) * 10^40
        + 4610678532426883694423738635372005421787) * 10^40
        + 1348194986275716386926075226207808740867) * 10^40
        + 2859812895586735155672602833660688466877) * 10^40
        + 3825938645104507609084649878708147384315) * 10^40
        + 1711206984288741132062649939797206118893) : ℚ) /
        (((((((((((22926166363001 * 10^40
        + 3081956321710908571381632481017187011774) * 10^40
        + 6402039074226517773534379816670194304523) * 10^40
        + 5367713076895515015814320796383947936843) * 10^40
        + 5820155829692885631883725648415839641949) * 10^40
        + 2932256366560468931359439475745045453723) * 10^40
        + 7211716810410125108874126630014602171303) * 10^40
        + 3408301493681969204721855833171051487220) * 10^40
        + 8664859105342997496087826836644648965237) * 10^40
        + 9966096762919173866993438771436939054032) * 10^40
        + 414117125072574988505228836662484433619) * 10^40
        + 3896161424863708113740072376527610707968)),
    (((-((((((((1740244167383056255746 * 10^40
        + 8721022320546419258215462921954104424858) * 10^40
        + 996533389527605533615835880014474546485) * 10^40
        + 8408728677680322010306056993552754487684) * 10^40
        + 2805199080729697798702059381634761543086) * 10^40
        + 3083606291550562837248843204963975141811) * 10^40
        + 7165074850020618758734458172412822471386) * 10^40
        + 7393009818619408571094830777789305302975) * 10^40
        + 7021773128988187281431844409227676540487)) : ℚ) /
        ((((((((417078 * 10^40
        + 69831387920944426737805818679749284257) * 10^40
        + 5324453826184385471189058194080916897831) * 10^40
        + 3739395863053770904223592309080487848215) * 10^40
        + 2323767560108408411532957459907251715007) * 10^40
        + 1487937696809576611164276211618973631388) * 10^40
        + 6255647409963100493827879479930853920535) * 10^40
        + 7230385033126758165455989380745410816524) * 10^40
        + 2393720342729576137446700068269669220352)))

noncomputable def neighborRightP011Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP011BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP011Center2557‖ ≤ neighborRightP011Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP011Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP011Input2557]
  have hs : compactExp2547 neighborRightP011Input2557 15 =
      (neighborRightP011Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP011Input2557 15).2 : ℝ) = neighborRightP011Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP011Error2557]
  have h := compactExp_error2547 neighborRightP011Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP011Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP011Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP011DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP011Factor2557 * embedPair2542 neighborRightP011Center2557‖ ≤
        (pairMagnitude2542 neighborRightP011Factor2557 : ℝ) * neighborRightP011Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP011Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP011Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP011BaseError2557
    (embedPair_magnitude2542 neighborRightP011Factor2557)

def neighborRightP012Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((6785390535256519649532381 : ℚ) /
        2361183241434822606848000000))

def neighborRightP012Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP012Factor2557 : RatPair2542 := ((((((((((((((2042141350510939500289689817194663
    *
    10^40
        + 9428392621712071148009690749717288836668) * 10^40
        + 4754151865543444917317546173210692444365) * 10^40
        + 9655342761761616257004519704181468880981) * 10^40
        + 3448012426299292485826763674586227297716) * 10^40
        + 387811416155003157217007559657010512758) * 10^40
        + 2499144087763802961325372044043661533975) * 10^40
        + 5987367482676130603306730841124059188479) * 10^40
        + 2735876360254830794634090879402558798076) * 10^40
        + 1937786500421071316556531942864794238159) * 10^40
        + 3484907952922252761375125354613568341320) * 10^40
        + 8798292343831038137545806494132777807749) : ℚ) /
        (((((((((((5731541590750 * 10^40
        + 3270489080427727142845408120254296752943) * 10^40
        + 6600509768556629443383594954167548576130) * 10^40
        + 8841928269223878753953580199095986984210) * 10^40
        + 8955038957423221407970931412103959910487) * 10^40
        + 3233064091640117232839859868936261363430) * 10^40
        + 9302929202602531277218531657503650542825) * 10^40
        + 8352075373420492301180463958292762871805) * 10^40
        + 2166214776335749374021956709161162241309) * 10^40
        + 4991524190729793466748359692859234763508) * 10^40
        + 103529281268143747126307209165621108404) * 10^40
        + 8474040356215927028435018094131902676992)),
    (((-((((((((239185477108757082669 * 10^40
        + 2582070570457572567127711203306842660108) * 10^40
        + 4976288964109584999977080081677579830117) * 10^40
        + 746924395201752117896013637216119550819) * 10^40
        + 2548641238881095062715976032754459247270) * 10^40
        + 5979816602137133470045883869297475846442) * 10^40
        + 5217523271795795850446550087464279539630) * 10^40
        + 943935126380071003004424918719990455190) * 10^40
        + 6273065344450757791331338423727166178075)) : ℚ) /
        ((((((((52134 * 10^40
        + 7508728923490118053342225727334968660532) * 10^40
        + 1915556728273048183898632274260114612228) * 10^40
        + 9217424482881721363027949038635060981026) * 10^40
        + 9040470945013551051441619682488406464375) * 10^40
        + 8935992212101197076395534526452371703923) * 10^40
        + 5781955926245387561728484934991356740066) * 10^40
        + 9653798129140844770681998672593176352065) * 10^40
        + 5299215042841197017180837508533708652544)))

noncomputable def neighborRightP012Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP012BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP012Center2557‖ ≤ neighborRightP012Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP012Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP012Input2557]
  have hs : compactExp2547 neighborRightP012Input2557 15 =
      (neighborRightP012Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP012Input2557 15).2 : ℝ) = neighborRightP012Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP012Error2557]
  have h := compactExp_error2547 neighborRightP012Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP012Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP012Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP012DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP012Factor2557 * embedPair2542 neighborRightP012Center2557‖ ≤
        (pairMagnitude2542 neighborRightP012Factor2557 : ℝ) * neighborRightP012Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP012Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP012Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP012BaseError2557
    (embedPair_magnitude2542 neighborRightP012Factor2557)

def neighborRightP013Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((73452149567042081226768819 : ℚ) /
        23611832414348226068480000000))

def neighborRightP013Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP013Factor2557 : RatPair2542 := ((((((((((((((8168565401966200128173669189702929
    *
    10^40
        + 5382766384011007770803421484024956309864) * 10^40
        + 9541661897688015520314513718005609296169) * 10^40
        + 356753715697916124525067262265967096555) * 10^40
        + 7639195765064615770699698955729900213002) * 10^40
        + 5695481173177394340592661359846835954156) * 10^40
        + 6952082207404307928565891282864904054399) * 10^40
        + 6973141874555948954918255125620947543113) * 10^40
        + 2230440831143161181811632704840917469572) * 10^40
        + 5368736239164301190887026341663041502233) * 10^40
        + 4134278653948884214014574170281985586620) * 10^40
        + 7051769374947871333593192630769894117421) : ℚ) /
        (((((((((((22926166363001 * 10^40
        + 3081956321710908571381632481017187011774) * 10^40
        + 6402039074226517773534379816670194304523) * 10^40
        + 5367713076895515015814320796383947936843) * 10^40
        + 5820155829692885631883725648415839641949) * 10^40
        + 2932256366560468931359439475745045453723) * 10^40
        + 7211716810410125108874126630014602171303) * 10^40
        + 3408301493681969204721855833171051487220) * 10^40
        + 8664859105342997496087826836644648965237) * 10^40
        + 9966096762919173866993438771436939054032) * 10^40
        + 414117125072574988505228836662484433619) * 10^40
        + 3896161424863708113740072376527610707968)),
    (((-((((((((2071354607821291569802 * 10^40
        + 3364594110177925307097637520576854453457) * 10^40
        + 4073256720048657713511662446993982079444) * 10^40
        + 84285661944119654056217428293892233383) * 10^40
        + 1908963685312117684105371614567744511247) * 10^40
        + 9131159775351747866055381755417749749914) * 10^40
        + 2814254484099466243838104590065184542610) * 10^40
        + 3076925791310966581694140973251924083652) * 10^40
        + 8138193320010540859203093236540446240665)) : ℚ) /
        ((((((((417078 * 10^40
        + 69831387920944426737805818679749284257) * 10^40
        + 5324453826184385471189058194080916897831) * 10^40
        + 3739395863053770904223592309080487848215) * 10^40
        + 2323767560108408411532957459907251715007) * 10^40
        + 1487937696809576611164276211618973631388) * 10^40
        + 6255647409963100493827879479930853920535) * 10^40
        + 7230385033126758165455989380745410816524) * 10^40
        + 2393720342729576137446700068269669220352)))

noncomputable def neighborRightP013Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP013BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP013Center2557‖ ≤ neighborRightP013Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP013Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP013Input2557]
  have hs : compactExp2547 neighborRightP013Input2557 15 =
      (neighborRightP013Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP013Input2557 15).2 : ℝ) = neighborRightP013Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP013Error2557]
  have h := compactExp_error2547 neighborRightP013Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP013Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP013Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP013DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP013Factor2557 * embedPair2542 neighborRightP013Center2557‖ ≤
        (pairMagnitude2542 neighborRightP013Factor2557 : ℝ) * neighborRightP013Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP013Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP013Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP013BaseError2557
    (embedPair_magnitude2542 neighborRightP013Factor2557)

def neighborRightP014Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((419125613659595683276618299 : ℚ) /
        118059162071741130342400000000))

def neighborRightP014Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP014Factor2557 : RatPair2542 := ((((((((((((((8168565401806250770138776900284694
    *
    10^40
        + 3878747775023617942509091545420765282767) * 10^40
        + 4993018713303668712475131213740900350233) * 10^40
        + 9638213130788209812254160314143262517645) * 10^40
        + 1155965385297398879249150699156932637486) * 10^40
        + 4867942027271046292534534384106944003360) * 10^40
        + 2990373074828133992377937110621071827143) * 10^40
        + 1608913429450489044504217505359300136893) * 10^40
        + 2098118229465472292278688595249834432710) * 10^40
        + 9635811074530554140606309488469122434325) * 10^40
        + 9447930350300710888243191380808496399578) * 10^40
        + 9513762435746165013141298080267732399333) : ℚ) /
        (((((((((((22926166363001 * 10^40
        + 3081956321710908571381632481017187011774) * 10^40
        + 6402039074226517773534379816670194304523) * 10^40
        + 5367713076895515015814320796383947936843) * 10^40
        + 5820155829692885631883725648415839641949) * 10^40
        + 2932256366560468931359439475745045453723) * 10^40
        + 7211716810410125108874126630014602171303) * 10^40
        + 3408301493681969204721855833171051487220) * 10^40
        + 8664859105342997496087826836644648965237) * 10^40
        + 9966096762919173866993438771436939054032) * 10^40
        + 414117125072574988505228836662484433619) * 10^40
        + 3896161424863708113740072376527610707968)),
    (((-((((((((2363873014541110834557 * 10^40
        + 6667227978211649648918346258733039251818) * 10^40
        + 9780622801383726471320404128764625949231) * 10^40
        + 1096580831544966240740597087752708812618) * 10^40
        + 9385775050407766486490505163823516897237) * 10^40
        + 8855840915917853114584078101172312705213) * 10^40
        + 9087233125668606687042207321296298872003) * 10^40
        + 1899348635098919637752811919807340516433) * 10^40
        + 8141194957727807565385482021523826578037)) : ℚ) /
        ((((((((417078 * 10^40
        + 69831387920944426737805818679749284257) * 10^40
        + 5324453826184385471189058194080916897831) * 10^40
        + 3739395863053770904223592309080487848215) * 10^40
        + 2323767560108408411532957459907251715007) * 10^40
        + 1487937696809576611164276211618973631388) * 10^40
        + 6255647409963100493827879479930853920535) * 10^40
        + 7230385033126758165455989380745410816524) * 10^40
        + 2393720342729576137446700068269669220352)))

noncomputable def neighborRightP014Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP014BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP014Center2557‖ ≤ neighborRightP014Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP014Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP014Input2557]
  have hs : compactExp2547 neighborRightP014Input2557 15 =
      (neighborRightP014Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP014Input2557 15).2 : ℝ) = neighborRightP014Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP014Error2557]
  have h := compactExp_error2547 neighborRightP014Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP014Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP014Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP014DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP014Factor2557 * embedPair2542 neighborRightP014Center2557‖ ≤
        (pairMagnitude2542 neighborRightP014Factor2557 : ℝ) * neighborRightP014Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP014Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP014Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP014BaseError2557
    (embedPair_magnitude2542 neighborRightP014Factor2557)

def neighborRightP015Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((456286966545542434888967823 : ℚ) /
        118059162071741130342400000000))

def neighborRightP015Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP015Factor2557 : RatPair2542 := ((((((((((((((8168565401678672247220040732457333
    *
    10^40
        + 6264091178450607579954848220273611276523) * 10^40
        + 5520867998930179809152669835421623320650) * 10^40
        + 5642175385773047226907139202105854796481) * 10^40
        + 5075633219336251576682273975585531522261) * 10^40
        + 6801147960795732807466362483873294920621) * 10^40
        + 464586697420763894099196963375576553949) * 10^40
        + 3609263964589822381394872413680347851645) * 10^40
        + 8134892808855717759830157719655809121934) * 10^40
        + 1988415951066929830949471630401934642793) * 10^40
        + 8355451429051039691289295022307813995370) * 10^40
        + 1589168569073363574320368601884663798669) : ℚ) /
        (((((((((((22926166363001 * 10^40
        + 3081956321710908571381632481017187011774) * 10^40
        + 6402039074226517773534379816670194304523) * 10^40
        + 5367713076895515015814320796383947936843) * 10^40
        + 5820155829692885631883725648415839641949) * 10^40
        + 2932256366560468931359439475745045453723) * 10^40
        + 7211716810410125108874126630014602171303) * 10^40
        + 3408301493681969204721855833171051487220) * 10^40
        + 8664859105342997496087826836644648965237) * 10^40
        + 9966096762919173866993438771436939054032) * 10^40
        + 414117125072574988505228836662484433619) * 10^40
        + 3896161424863708113740072376527610707968)),
    (((-((((((((2573463448544991809439 * 10^40
        + 2381048121372844082095229494832155470021) * 10^40
        + 3840601080303781271737094265456776417216) * 10^40
        + 5279344423473968190808422886353841129014) * 10^40
        + 7462579487940377389177830533880291319534) * 10^40
        + 3044659898365681774372903731803022673523) * 10^40
        + 5285100923715167568343806189639221899645) * 10^40
        + 3356925856425474527337794802724204316556) * 10^40
        + 6787027293049325228780204311159973108713)) : ℚ) /
        ((((((((417078 * 10^40
        + 69831387920944426737805818679749284257) * 10^40
        + 5324453826184385471189058194080916897831) * 10^40
        + 3739395863053770904223592309080487848215) * 10^40
        + 2323767560108408411532957459907251715007) * 10^40
        + 1487937696809576611164276211618973631388) * 10^40
        + 6255647409963100493827879479930853920535) * 10^40
        + 7230385033126758165455989380745410816524) * 10^40
        + 2393720342729576137446700068269669220352)))

noncomputable def neighborRightP015Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP015BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP015Center2557‖ ≤ neighborRightP015Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP015Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP015Input2557]
  have hs : compactExp2547 neighborRightP015Input2557 15 =
      (neighborRightP015Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP015Input2557 15).2 : ℝ) = neighborRightP015Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP015Error2557]
  have h := compactExp_error2547 neighborRightP015Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP015Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP015Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP015DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP015Factor2557 * embedPair2542 neighborRightP015Center2557‖ ≤
        (pairMagnitude2542 neighborRightP015Factor2557 : ℝ) * neighborRightP015Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP015Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP015Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP015BaseError2557
    (embedPair_magnitude2542 neighborRightP015Factor2557)

def neighborRightP016Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((241571331091476180442591281 : ℚ) /
        59029581035870565171200000000))

def neighborRightP016Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP016Factor2557 : RatPair2542 := ((((((((((((((2042141350394932946561898598261592
    *
    10^40
        + 1226840596254331425801883744271513356349) * 10^40
        + 21080969011234170935999562457347647954) * 10^40
        + 3431282803255687848859484906741961042957) * 10^40
        + 641040751095049489306945112409585674639) * 10^40
        + 3005514778030764960399202894297546463697) * 10^40
        + 9899706475592456430430482528086133084698) * 10^40
        + 3437368327119515215081143524238742696530) * 10^40
        + 3472493360601671228509312638246696155979) * 10^40
        + 3640399421606493923713709457605386282252) * 10^40
        + 3807753617238557046361092586899891525731) * 10^40
        + 9804063204717671186294840081671355495181) : ℚ) /
        (((((((((((5731541590750 * 10^40
        + 3270489080427727142845408120254296752943) * 10^40
        + 6600509768556629443383594954167548576130) * 10^40
        + 8841928269223878753953580199095986984210) * 10^40
        + 8955038957423221407970931412103959910487) * 10^40
        + 3233064091640117232839859868936261363430) * 10^40
        + 9302929202602531277218531657503650542825) * 10^40
        + 8352075373420492301180463958292762871805) * 10^40
        + 2166214776335749374021956709161162241309) * 10^40
        + 4991524190729793466748359692859234763508) * 10^40
        + 103529281268143747126307209165621108404) * 10^40
        + 8474040356215927028435018094131902676992)),
    (((-((((((((20036248997823836833 * 10^40
        + 464893411061584319987132238951645935435) * 10^40
        + 934447303967469039474261427019559726988) * 10^40
        + 9804202167367285707945685647566448491078) * 10^40
        + 9762912353790596071687296307444286877022) * 10^40
        + 7198064728622401367142442061304748363010) * 10^40
        + 4698111206317152863614143519226892050182) * 10^40
        + 1978743489612364083488843924150384517700) * 10^40
        + 9650505729720939677327123524992733813607)) : ℚ) /
        ((((((((3066 * 10^40
        + 7500513466087654003137777983960880509443) * 10^40
        + 700915101663120481405801898485889094836) * 10^40
        + 9953966146051865962531055825802062410648) * 10^40
        + 6414145349706679473614212922499318027316) * 10^40
        + 2290352483064776298611502030967786570819) * 10^40
        + 340115054485022797748734407940668043533) * 10^40
        + 3509046948772990868863646980740775079533) * 10^40
        + 2664659708402423353951813971090218156032)))

noncomputable def neighborRightP016Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP016BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP016Center2557‖ ≤ neighborRightP016Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP016Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP016Input2557]
  have hs : compactExp2547 neighborRightP016Input2557 15 =
      (neighborRightP016Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP016Input2557 15).2 : ℝ) = neighborRightP016Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP016Error2557]
  have h := compactExp_error2547 neighborRightP016Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP016Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP016Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP016DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP016Factor2557 * embedPair2542 neighborRightP016Center2557‖ ≤
        (pairMagnitude2542 neighborRightP016Factor2557 : ℝ) * neighborRightP016Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP016Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP016Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP016BaseError2557
    (embedPair_magnitude2542 neighborRightP016Factor2557)

def neighborRightP017Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((535308171979337431536686643 : ℚ) /
        118059162071741130342400000000))

def neighborRightP017Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP017Factor2557 : RatPair2542 := ((((((((((((((8168565401371380208251231903337141
    *
    10^40
        + 7624577359072592205461395342627525013799) * 10^40
        + 4729084197653221987821814632027575295639) * 10^40
        + 5716005582262084055527019313385138088794) * 10^40
        + 1928101605360974341413279427873923485605) * 10^40
        + 916265909582712441152581354394931170258) * 10^40
        + 2894516136660081280262026361340071798838) * 10^40
        + 5382621138701516501781567005248058259791) * 10^40
        + 6839500918674659822272949928124024357466) * 10^40
        + 2242568452383819076428551541673192891057) * 10^40
        + 9887507203421768687227871930211735409971) * 10^40
        + 3679854452627850158290929127101094253109) : ℚ) /
        (((((((((((22926166363001 * 10^40
        + 3081956321710908571381632481017187011774) * 10^40
        + 6402039074226517773534379816670194304523) * 10^40
        + 5367713076895515015814320796383947936843) * 10^40
        + 5820155829692885631883725648415839641949) * 10^40
        + 2932256366560468931359439475745045453723) * 10^40
        + 7211716810410125108874126630014602171303) * 10^40
        + 3408301493681969204721855833171051487220) * 10^40
        + 8664859105342997496087826836644648965237) * 10^40
        + 9966096762919173866993438771436939054032) * 10^40
        + 414117125072574988505228836662484433619) * 10^40
        + 3896161424863708113740072376527610707968)),
    (((-((((((((3019143905687267070996 * 10^40
        + 3587019626969482409829638181524981441335) * 10^40
        + 4027728378871378376735224172982122762396) * 10^40
        + 4762536064400012368806849542246545837659) * 10^40
        + 3904495182481898221732673973328408169741) * 10^40
        + 1181546241947489696372334999138009744377) * 10^40
        + 2337894428846286528085904367072367702248) * 10^40
        + 7686164346202649206131420634885196686097) * 10^40
        + 5546551571607254370446296807413145638093)) : ℚ) /
        ((((((((417078 * 10^40
        + 69831387920944426737805818679749284257) * 10^40
        + 5324453826184385471189058194080916897831) * 10^40
        + 3739395863053770904223592309080487848215) * 10^40
        + 2323767560108408411532957459907251715007) * 10^40
        + 1487937696809576611164276211618973631388) * 10^40
        + 6255647409963100493827879479930853920535) * 10^40
        + 7230385033126758165455989380745410816524) * 10^40
        + 2393720342729576137446700068269669220352)))

noncomputable def neighborRightP017Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP017BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP017Center2557‖ ≤ neighborRightP017Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP017Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP017Input2557]
  have hs : compactExp2547 neighborRightP017Input2557 15 =
      (neighborRightP017Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP017Input2557 15).2 : ℝ) = neighborRightP017Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP017Error2557]
  have h := compactExp_error2547 neighborRightP017Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP017Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP017Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP017DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP017Factor2557 * embedPair2542 neighborRightP017Center2557‖ ≤
        (pairMagnitude2542 neighborRightP017Factor2557 : ℝ) * neighborRightP017Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP017Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP017Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP017BaseError2557
    (embedPair_magnitude2542 neighborRightP017Factor2557)

def neighborRightP018Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((138757710302715355185282117 : ℚ) /
        29514790517935282585600000000))

def neighborRightP018Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP018Factor2557 : RatPair2542 := ((((((((((((((510535337580440414555415823066706 *
    10^40
        + 4556307830537153427791958481103399966803) * 10^40
        + 7542894233934770861708952582060734681277) * 10^40
        + 8274160235580191271064594225575749352462) * 10^40
        + 7485307838949371930968050625932013233801) * 10^40
        + 3796210272498370603896900990928368294941) * 10^40
        + 9838694100865734764975984127491760283247) * 10^40
        + 2895478298582257497805453287144965631952) * 10^40
        + 4014764240803815810479773169457926474875) * 10^40
        + 2355575193057619182554369006466422832509) * 10^40
        + 4065562347162720612629120715920638569481) * 10^40
        + 8960196438569283363432857812301996786149) : ℚ) /
        (((((((((((1432885397687 * 10^40
        + 5817622270106931785711352030063574188235) * 10^40
        + 9150127442139157360845898738541887144032) * 10^40
        + 7210482067305969688488395049773996746052) * 10^40
        + 7238759739355805351992732853025989977621) * 10^40
        + 8308266022910029308209964967234065340857) * 10^40
        + 7325732300650632819304632914375912635706) * 10^40
        + 4588018843355123075295115989573190717951) * 10^40
        + 3041553694083937343505489177290290560327) * 10^40
        + 3747881047682448366687089923214808690877) * 10^40
        + 25882320317035936781576802291405277101) * 10^40
        + 2118510089053981757108754523532975669248)),
    (((-((((((((48912187100336796408 * 10^40
        + 7907418242116900868450127070886463830294) * 10^40
        + 7088614257547641398280766907843228042183) * 10^40
        + 6756025006789151846291655239261403688745) * 10^40
        + 7971269396782122406338737637912752679653) * 10^40
        + 1538019331498235923677083321784935485986) * 10^40
        + 5009839297561161960074940726637971666656) * 10^40
        + 6821745351164212778461689251597237238830) * 10^40
        + 8737140635243516553237242438091490853387)) : ℚ) /
        ((((((((6516 * 10^40
        + 8438591115436264756667778215916871082566) * 10^40
        + 5239444591034131022987329034282514326528) * 10^40
        + 6152178060360215170378493629829382622628) * 10^40
        + 3630058868126693881430202460311050808046) * 10^40
        + 9866999026512649634549441815806546462990) * 10^40
        + 4472744490780673445216060616873919592508) * 10^40
        + 3706724766142605596335249834074147044008) * 10^40
        + 1912401880355149627147604688566713581568)))

noncomputable def neighborRightP018Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP018BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP018Center2557‖ ≤ neighborRightP018Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP018Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP018Input2557]
  have hs : compactExp2547 neighborRightP018Input2557 15 =
      (neighborRightP018Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP018Input2557 15).2 : ℝ) = neighborRightP018Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP018Error2557]
  have h := compactExp_error2547 neighborRightP018Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP018Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP018Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP018DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP018Factor2557 * embedPair2542 neighborRightP018Center2557‖ ≤
        (pairMagnitude2542 neighborRightP018Factor2557 : ℝ) * neighborRightP018Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP018Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP018Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP018BaseError2557
    (embedPair_magnitude2542 neighborRightP018Factor2557)

def neighborRightP019Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((29533753606550223310219719 : ℚ) /
        5902958103587056517120000000))

def neighborRightP019Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP019Factor2557 : RatPair2542 := ((((((((((((((510535337570430838348176901114412 *
    10^40
        + 9102277424084503574760101575307717690927) * 10^40
        + 3312630465015545624411832223376831222359) * 10^40
        + 6116115064584146772451389664316404379793) * 10^40
        + 4085842265180370553472923313056356115063) * 10^40
        + 8213343022015421280117001449681077867522) * 10^40
        + 3882624115955931156929859255825342209747) * 10^40
        + 4953279414196459673609769877580806960483) * 10^40
        + 3787323931985890678530130571643762030251) * 10^40
        + 6692087006272487825680998829243256984938) * 10^40
        + 6835678016740182630158225516405563484409) * 10^40
        + 7025076589521884181241065966847840122581) : ℚ) /
        (((((((((((1432885397687 * 10^40
        + 5817622270106931785711352030063574188235) * 10^40
        + 9150127442139157360845898738541887144032) * 10^40
        + 7210482067305969688488395049773996746052) * 10^40
        + 7238759739355805351992732853025989977621) * 10^40
        + 8308266022910029308209964967234065340857) * 10^40
        + 7325732300650632819304632914375912635706) * 10^40
        + 4588018843355123075295115989573190717951) * 10^40
        + 3041553694083937343505489177290290560327) * 10^40
        + 3747881047682448366687089923214808690877) * 10^40
        + 25882320317035936781576802291405277101) * 10^40
        + 2118510089053981757108754523532975669248)),
    (((-((((((((52053341000806940410 * 10^40
        + 5899611229173859870979662775446513040383) * 10^40
        + 5791609442315179920707950237694492985147) * 10^40
        + 8991987809594237038747597771895212325938) * 10^40
        + 355988772798428785153476232588507597492) * 10^40
        + 1347856260477306040016395708460319345000) * 10^40
        + 1076358002023677519080577968472640574611) * 10^40
        + 4016291677674782648767018161457285157379) * 10^40
        + 7722500571768091310105333763066097605565)) : ℚ) /
        ((((((((6516 * 10^40
        + 8438591115436264756667778215916871082566) * 10^40
        + 5239444591034131022987329034282514326528) * 10^40
        + 6152178060360215170378493629829382622628) * 10^40
        + 3630058868126693881430202460311050808046) * 10^40
        + 9866999026512649634549441815806546462990) * 10^40
        + 4472744490780673445216060616873919592508) * 10^40
        + 3706724766142605596335249834074147044008) * 10^40
        + 1912401880355149627147604688566713581568)))

noncomputable def neighborRightP019Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP019BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP019Center2557‖ ≤ neighborRightP019Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP019Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP019Input2557]
  have hs : compactExp2547 neighborRightP019Input2557 15 =
      (neighborRightP019Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP019Input2557 15).2 : ℝ) = neighborRightP019Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP019Error2557]
  have h := compactExp_error2547 neighborRightP019Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP019Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP019Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP019DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP019Factor2557 * embedPair2542 neighborRightP019Center2557‖ ≤
        (pairMagnitude2542 neighborRightP019Factor2557 : ℝ) * neighborRightP019Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP019Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP019Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP019BaseError2557
    (embedPair_magnitude2542 neighborRightP019Factor2557)

def neighborRightP020Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((629435323401138262557665571 : ℚ) /
        118059162071741130342400000000))

def neighborRightP020Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP020Factor2557 : RatPair2542 := ((((((((((((((8168565400941429687384507703729271
    *
    10^40
        + 9919512851303859718197965922201634955551) * 10^40
        + 9011712003177227144046749682819689277742) * 10^40
        + 1768072145234157500024851646185849923953) * 10^40
        + 8320891248218983343911152607823238512116) * 10^40
        + 6993878419972674128473137683741037485109) * 10^40
        + 4000885563634759592138249867681706183937) * 10^40
        + 8544017427503643835182607075025144357586) * 10^40
        + 6554343137617035305130170346998692823482) * 10^40
        + 2842591600495684779772413160031260671386) * 10^40
        + 6168148851404539817251383889551596235634) * 10^40
        + 9697343933658098490919084617589041597013) : ℚ) /
        (((((((((((22926166363001 * 10^40
        + 3081956321710908571381632481017187011774) * 10^40
        + 6402039074226517773534379816670194304523) * 10^40
        + 5367713076895515015814320796383947936843) * 10^40
        + 5820155829692885631883725648415839641949) * 10^40
        + 2932256366560468931359439475745045453723) * 10^40
        + 7211716810410125108874126630014602171303) * 10^40
        + 3408301493681969204721855833171051487220) * 10^40
        + 8664859105342997496087826836644648965237) * 10^40
        + 9966096762919173866993438771436939054032) * 10^40
        + 414117125072574988505228836662484433619) * 10^40
        + 3896161424863708113740072376527610707968)),
    (((-((((((((3550022062306722612750 * 10^40
        + 3240923921054705511469795518868513561790) * 10^40
        + 9884521662378463825287441660690789141197) * 10^40
        + 2802880502660342686947230631257655294874) * 10^40
        + 6287210544722388685350459447485896857907) * 10^40
        + 4276388875627349274379699420542007443595) * 10^40
        + 8107349877298408122968742841098489577519) * 10^40
        + 1132767640975380015395559837890655971176) * 10^40
        + 6490021744376671543624326208048989596413)) : ℚ) /
        ((((((((417078 * 10^40
        + 69831387920944426737805818679749284257) * 10^40
        + 5324453826184385471189058194080916897831) * 10^40
        + 3739395863053770904223592309080487848215) * 10^40
        + 2323767560108408411532957459907251715007) * 10^40
        + 1487937696809576611164276211618973631388) * 10^40
        + 6255647409963100493827879479930853920535) * 10^40
        + 7230385033126758165455989380745410816524) * 10^40
        + 2393720342729576137446700068269669220352)))

noncomputable def neighborRightP020Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP020BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP020Center2557‖ ≤ neighborRightP020Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP020Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP020Input2557]
  have hs : compactExp2547 neighborRightP020Input2557 15 =
      (neighborRightP020Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP020Input2557 15).2 : ℝ) = neighborRightP020Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP020Error2557]
  have h := compactExp_error2547 neighborRightP020Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP020Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP020Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP020DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP020Factor2557 * embedPair2542 neighborRightP020Center2557‖ ≤
        (pairMagnitude2542 neighborRightP020Factor2557 : ℝ) * neighborRightP020Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP020Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP020Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP020BaseError2557
    (embedPair_magnitude2542 neighborRightP020Factor2557)

def neighborRightP021Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((661782268241419174231706883 : ℚ) /
        118059162071741130342400000000))

def neighborRightP021Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP021Factor2557 : RatPair2542 := ((((((((((((((8168565400777632676507202509525587
    *
    10^40
        + 7763119941091157750735982957712593993227) * 10^40
        + 1611998945491512960630828620674348502166) * 10^40
        + 9819347710496600620492584505003410949507) * 10^40
        + 9443588101548460280059421216862471326736) * 10^40
        + 3598416446111177277434932000352387032379) * 10^40
        + 388767558348870269077676297141917493099) * 10^40
        + 6554669030663328706642051090467437144027) * 10^40
        + 1250137912716440351551721121852886917997) * 10^40
        + 2221459818041476647587306554921849792181) * 10^40
        + 8371508437524109176175691373362085777185) * 10^40
        + 3874374596017646661340430987157050403989) : ℚ) /
        (((((((((((22926166363001 * 10^40
        + 3081956321710908571381632481017187011774) * 10^40
        + 6402039074226517773534379816670194304523) * 10^40
        + 5367713076895515015814320796383947936843) * 10^40
        + 5820155829692885631883725648415839641949) * 10^40
        + 2932256366560468931359439475745045453723) * 10^40
        + 7211716810410125108874126630014602171303) * 10^40
        + 3408301493681969204721855833171051487220) * 10^40
        + 8664859105342997496087826836644648965237) * 10^40
        + 9966096762919173866993438771436939054032) * 10^40
        + 414117125072574988505228836662484433619) * 10^40
        + 3896161424863708113740072376527610707968)),
    (((-((((((((3732459182621942232411 * 10^40
        + 2875219957710396267566626019420035671717) * 10^40
        + 3261177375884337241322578935404041191866) * 10^40
        + 1171792188999373774222592380871583428000) * 10^40
        + 9665494386037746748031689299055618796699) * 10^40
        + 3953824528316653844287426490939979285380) * 10^40
        + 2487116535757073167928086959089716456223) * 10^40
        + 73810726818992191269884588890696645011) * 10^40
        + 8446559131189998057559344709220667733853)) : ℚ) /
        ((((((((417078 * 10^40
        + 69831387920944426737805818679749284257) * 10^40
        + 5324453826184385471189058194080916897831) * 10^40
        + 3739395863053770904223592309080487848215) * 10^40
        + 2323767560108408411532957459907251715007) * 10^40
        + 1487937696809576611164276211618973631388) * 10^40
        + 6255647409963100493827879479930853920535) * 10^40
        + 7230385033126758165455989380745410816524) * 10^40
        + 2393720342729576137446700068269669220352)))

noncomputable def neighborRightP021Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP021BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP021Center2557‖ ≤ neighborRightP021Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP021Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP021Input2557]
  have hs : compactExp2547 neighborRightP021Input2557 15 =
      (neighborRightP021Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP021Input2557 15).2 : ℝ) = neighborRightP021Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP021Error2557]
  have h := compactExp_error2547 neighborRightP021Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP021Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP021Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP021DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP021Factor2557 * embedPair2542 neighborRightP021Center2557‖ ≤
        (pairMagnitude2542 neighborRightP021Factor2557 : ℝ) * neighborRightP021Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP021Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP021Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP021BaseError2557
    (embedPair_magnitude2542 neighborRightP021Factor2557)

def neighborRightP022Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((135667725494164983963605697 : ℚ) /
        23611832414348226068480000000))

def neighborRightP022Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP022Factor2557 : RatPair2542 := ((((((((((((((8168565400690620087770320170085536
    *
    10^40
        + 7908517159602233676732172222734217486417) * 10^40
        + 4515232000860633532982352397804509099331) * 10^40
        + 5433158255492399619499988586772082121385) * 10^40
        + 4366448198931364642083935930027283605461) * 10^40
        + 8202887676408655723754978155855229206789) * 10^40
        + 4231303171196481058311218686695287590936) * 10^40
        + 6251981506726197634345541510720308689518) * 10^40
        + 826986549353147488541440957358231425711) * 10^40
        + 4962355443186444595026972272930642506427) * 10^40
        + 2706976122767522873271634174631945695592) * 10^40
        + 9289447325332955888602687941642767086821) : ℚ) /
        (((((((((((22926166363001 * 10^40
        + 3081956321710908571381632481017187011774) * 10^40
        + 6402039074226517773534379816670194304523) * 10^40
        + 5367713076895515015814320796383947936843) * 10^40
        + 5820155829692885631883725648415839641949) * 10^40
        + 2932256366560468931359439475745045453723) * 10^40
        + 7211716810410125108874126630014602171303) * 10^40
        + 3408301493681969204721855833171051487220) * 10^40
        + 8664859105342997496087826836644648965237) * 10^40
        + 9966096762919173866993438771436939054032) * 10^40
        + 414117125072574988505228836662484433619) * 10^40
        + 3896161424863708113740072376527610707968)),
    (((-((((((((3825837228542997014250 * 10^40
        + 517591810812882954785265334265023845032) * 10^40
        + 7614652171619590879823499707776877765991) * 10^40
        + 4692310065710467064524447421017086105239) * 10^40
        + 7765370706191617154223205532155677057127) * 10^40
        + 9560979116403286908144344698463774373865) * 10^40
        + 5676574467613394522119234459242116547710) * 10^40
        + 3534503985088912247121667318716712528600) * 10^40
        + 1723549074256213134350777088787317632395)) : ℚ) /
        ((((((((417078 * 10^40
        + 69831387920944426737805818679749284257) * 10^40
        + 5324453826184385471189058194080916897831) * 10^40
        + 3739395863053770904223592309080487848215) * 10^40
        + 2323767560108408411532957459907251715007) * 10^40
        + 1487937696809576611164276211618973631388) * 10^40
        + 6255647409963100493827879479930853920535) * 10^40
        + 7230385033126758165455989380745410816524) * 10^40
        + 2393720342729576137446700068269669220352)))

noncomputable def neighborRightP022Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP022BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP022Center2557‖ ≤ neighborRightP022Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP022Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP022Input2557]
  have hs : compactExp2547 neighborRightP022Input2557 15 =
      (neighborRightP022Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP022Input2557 15).2 : ℝ) = neighborRightP022Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP022Error2557]
  have h := compactExp_error2547 neighborRightP022Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP022Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP022Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP022DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP022Factor2557 * embedPair2542 neighborRightP022Center2557‖ ≤
        (pairMagnitude2542 neighborRightP022Factor2557 : ℝ) * neighborRightP022Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP022Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP022Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP022BaseError2557
    (embedPair_magnitude2542 neighborRightP022Factor2557)

def neighborRightP023Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((363036843833529947066478597 : ℚ) /
        59029581035870565171200000000))

def neighborRightP023Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP023Factor2557 : RatPair2542 := ((((((((((((((2042141350106927784017284270226621
    *
    10^40
        + 2831847526525958441126879459065635379626) * 10^40
        + 6405798494315339397476327884681499206026) * 10^40
        + 835962477759174973534632582888330235257) * 10^40
        + 8984116068743976896884816334773514613537) * 10^40
        + 9226054045051263865763162268603616359243) * 10^40
        + 2774305388964720268100292211153594299638) * 10^40
        + 4877018211766162856107420907220466406003) * 10^40
        + 2634178190842927978936056479103555971508) * 10^40
        + 92895201636311130261430151808055929523) * 10^40
        + 6370728348151292410229345069822173716907) * 10^40
        + 1997199795277445526150258003104436070757) : ℚ) /
        (((((((((((5731541590750 * 10^40
        + 3270489080427727142845408120254296752943) * 10^40
        + 6600509768556629443383594954167548576130) * 10^40
        + 8841928269223878753953580199095986984210) * 10^40
        + 8955038957423221407970931412103959910487) * 10^40
        + 3233064091640117232839859868936261363430) * 10^40
        + 9302929202602531277218531657503650542825) * 10^40
        + 8352075373420492301180463958292762871805) * 10^40
        + 2166214776335749374021956709161162241309) * 10^40
        + 4991524190729793466748359692859234763508) * 10^40
        + 103529281268143747126307209165621108404) * 10^40
        + 8474040356215927028435018094131902676992)),
    (((-((((((((511882935829804275982 * 10^40
        + 129278714176851776001291316279777652274) * 10^40
        + 1010280517580781792887790260316510359440) * 10^40
        + 969887238714483985051730974760341693851) * 10^40
        + 2278778094751401814835880704395410381511) * 10^40
        + 3242259298027819974850248743351511858610) * 10^40
        + 2238523864676896759120344842295782082782) * 10^40
        + 6796729622075371428267787155658563434295) * 10^40
        + 7904685256919983586236148433403303963339)) : ℚ) /
        ((((((((52134 * 10^40
        + 7508728923490118053342225727334968660532) * 10^40
        + 1915556728273048183898632274260114612228) * 10^40
        + 9217424482881721363027949038635060981026) * 10^40
        + 9040470945013551051441619682488406464375) * 10^40
        + 8935992212101197076395534526452371703923) * 10^40
        + 5781955926245387561728484934991356740066) * 10^40
        + 9653798129140844770681998672593176352065) * 10^40
        + 5299215042841197017180837508533708652544)))

noncomputable def neighborRightP023Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP023BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP023Center2557‖ ≤ neighborRightP023Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP023Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP023Input2557]
  have hs : compactExp2547 neighborRightP023Input2557 15 =
      (neighborRightP023Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP023Input2557 15).2 : ℝ) = neighborRightP023Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP023Error2557]
  have h := compactExp_error2547 neighborRightP023Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP023Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP023Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP023DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP023Factor2557 * embedPair2542 neighborRightP023Center2557‖ ≤
        (pairMagnitude2542 neighborRightP023Factor2557 : ℝ) * neighborRightP023Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP023Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP023Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP023BaseError2557
    (embedPair_magnitude2542 neighborRightP023Factor2557)

def neighborRightP024Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((374005394131059804721629723 : ℚ) /
        59029581035870565171200000000))

def neighborRightP024Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP024Factor2557 : RatPair2542 := ((((((((((((((2042141350075223724267735865638812
    *
    10^40
        + 864402679551910814186520289706362309066) * 10^40
        + 2915543289636622641223232016086641365082) * 10^40
        + 7557929702047099693059267368432801032969) * 10^40
        + 5587056139183578464098679446823695077764) * 10^40
        + 4510351937771936227620199189877689727124) * 10^40
        + 1104781449001153839035391867564437500068) * 10^40
        + 4794126404047817325440215429843520592318) * 10^40
        + 2981109914505745353615174747636757742674) * 10^40
        + 4165200840148873765060832251998942806637) * 10^40
        + 8702131648030017465807475278792546055503) * 10^40
        + 8721346867071836674743258946820544098597) : ℚ) /
        (((((((((((5731541590750 * 10^40
        + 3270489080427727142845408120254296752943) * 10^40
        + 6600509768556629443383594954167548576130) * 10^40
        + 8841928269223878753953580199095986984210) * 10^40
        + 8955038957423221407970931412103959910487) * 10^40
        + 3233064091640117232839859868936261363430) * 10^40
        + 9302929202602531277218531657503650542825) * 10^40
        + 8352075373420492301180463958292762871805) * 10^40
        + 2166214776335749374021956709161162241309) * 10^40
        + 4991524190729793466748359692859234763508) * 10^40
        + 103529281268143747126307209165621108404) * 10^40
        + 8474040356215927028435018094131902676992)),
    (((-((((((((527348621539491799902 * 10^40
        + 8884618936456364759316148538573556153066) * 10^40
        + 6528163322952205945957307627563086427102) * 10^40
        + 2461555669948729710034320137386104626491) * 10^40
        + 4660296243010959817677862771480570427863) * 10^40
        + 6908772152548602113640710930182427288446) * 10^40
        + 7410596144948862032205629855197434848689) * 10^40
        + 7036834385542832037744595211285845184384) * 10^40
        + 8278841556045533873666040123638720616661)) : ℚ) /
        ((((((((52134 * 10^40
        + 7508728923490118053342225727334968660532) * 10^40
        + 1915556728273048183898632274260114612228) * 10^40
        + 9217424482881721363027949038635060981026) * 10^40
        + 9040470945013551051441619682488406464375) * 10^40
        + 8935992212101197076395534526452371703923) * 10^40
        + 5781955926245387561728484934991356740066) * 10^40
        + 9653798129140844770681998672593176352065) * 10^40
        + 5299215042841197017180837508533708652544)))

noncomputable def neighborRightP024Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP024BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP024Center2557‖ ≤ neighborRightP024Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP024Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP024Input2557]
  have hs : compactExp2547 neighborRightP024Input2557 15 =
      (neighborRightP024Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP024Input2557 15).2 : ℝ) = neighborRightP024Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP024Error2557]
  have h := compactExp_error2547 neighborRightP024Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP024Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP024Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP024DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP024Factor2557 * embedPair2542 neighborRightP024Center2557‖ ≤
        (pairMagnitude2542 neighborRightP024Factor2557 : ℝ) * neighborRightP024Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP024Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP024Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP024BaseError2557
    (embedPair_magnitude2542 neighborRightP024Factor2557)

def neighborRightP025Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((12117435734886672992717097 : ℚ) /
        1844674407370955161600000000))

def neighborRightP025Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP025Factor2557 : RatPair2542 := ((((((((((((((1994278662142714220704414558648 *
    10^40
        + 6278738704408330949708647616880403744389) * 10^40
        + 3633423951197182324174710584493403774473) * 10^40
        + 4702031441291332571796652761821672088903) * 10^40
        + 2686410931935394159171430216387534523203) * 10^40
        + 6893954119895151395904717857550036305984) * 10^40
        + 3561819913020974149856188739143326375870) * 10^40
        + 1946148204997403653867537428117510284435) * 10^40
        + 7401602602742194464384370484991276679957) * 10^40
        + 6328893745910008981468773231661878523590) * 10^40
        + 2261442076155264328888118537176629412777) * 10^40
        + 9901118835181969512795765410954686774909) : ℚ) /
        (((((((((((5597208584 * 10^40
        + 7171162586992605202287934968867435836672) * 10^40
        + 7965430185320856083440804291947429246656) * 10^40
        + 3778165945575413944095657793163179674789) * 10^40
        + 2684526405231858614656221612707132773350) * 10^40
        + 852766664151992301985195175653258067737) * 10^40
        + 7255178641799416534450408722321780908733) * 10^40
        + 2283546948606855949512871546834270276241) * 10^40
        + 9972818569117515380248068317098790197501) * 10^40
        + 2788077660342509563932371445012557846448) * 10^40
        + 7382913602813738421628053034383950801863) * 10^40
        + 6766087930035367116238706072357550686208)),
    (((-((((((((16685173142214247 * 10^40
        + 5243977115433229975679857572793523533324) * 10^40
        + 3466666150626792112503633976511303665640) * 10^40
        + 8372447906696543884226911502479136980107) * 10^40
        + 2803862608683508323355787745006318940713) * 10^40
        + 5773619366947436580168503318650725749881) * 10^40
        + 5398355121515546680917397241053236461075) * 10^40
        + 4395082157804334733469271767626640448139) * 10^40
        + 3534215216632296060769504629762840223087)) : ℚ) /
        ((((((((1 * 10^40
        + 5910263327909042056825358344290995329854) * 10^40
        + 1422177598777107942144284015877510379474) * 10^40
        + 2501501996596767630656830686921345064116) * 10^40
        + 8526276869840851243623396045522536877638) * 10^40
        + 6833463622809207189852184922318312145132) * 10^40
        + 5660271666135444500352835952299041484275) * 10^40
        + 5147389337101109034569417785604022008555) * 10^40
        + 6660623144990321081451940333175919607808)))

noncomputable def neighborRightP025Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP025BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP025Center2557‖ ≤ neighborRightP025Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP025Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP025Input2557]
  have hs : compactExp2547 neighborRightP025Input2557 15 =
      (neighborRightP025Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP025Input2557 15).2 : ℝ) = neighborRightP025Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP025Error2557]
  have h := compactExp_error2547 neighborRightP025Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP025Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP025Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP025DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP025Factor2557 * embedPair2542 neighborRightP025Center2557‖ ≤
        (pairMagnitude2542 neighborRightP025Factor2557 : ℝ) * neighborRightP025Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP025Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP025Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP025BaseError2557
    (embedPair_magnitude2542 neighborRightP025Factor2557)

def neighborRightP026Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((25113280636521318884391333 : ℚ) /
        3689348814741910323200000000))

def neighborRightP026Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP026Factor2557 : RatPair2542 := ((((((((((((((7977114648400859974209934804496 *
    10^40
        + 7517314220342700320472499184084035136297) * 10^40
        + 369829505338544901791068998106259864109) * 10^40
        + 2095555962581844365023720224782723913797) * 10^40
        + 5104376102618719118347316134623962148415) * 10^40
        + 4113482614388671399670021976119882422779) * 10^40
        + 3287012815393371561984749832744566701102) * 10^40
        + 8418009216357088876714666377612970638239) * 10^40
        + 7951782521096167189656416074849504132663) * 10^40
        + 9160208671914284476632959622853097150310) * 10^40
        + 9224718506945521913128791019220853575433) * 10^40
        + 914591369591245680179590090641306232997) : ℚ) /
        (((((((((((22388834338 * 10^40
        + 8684650347970420809151739875469743346691) * 10^40
        + 1861720741283424333763217167789716986625) * 10^40
        + 5112663782301655776382631172652718699157) * 10^40
        + 738105620927434458624886450828531093400) * 10^40
        + 3411066656607969207940780702613032270950) * 10^40
        + 9020714567197666137801634889287123634932) * 10^40
        + 9134187794427423798051486187337081104967) * 10^40
        + 9891274276470061520992273268395160790005) * 10^40
        + 1152310641370038255729485780050231385794) * 10^40
        + 9531654411254953686512212137535803207454) * 10^40
        + 7064351720141468464954824289430202744832)),
    (((-((((((((138319507445624266 * 10^40
        + 2323719378842815397065772224572453428232) * 10^40
        + 5933217109216798596659439192198388212861) * 10^40
        + 4665961749339434497827153126404932043662) * 10^40
        + 399885354163951971250789603971707331957) * 10^40
        + 8437248050884690853538702009679927493465) * 10^40
        + 7577298806194719034047751579063311474252) * 10^40
        + 1208547088370843843726608593969611806414) * 10^40
        + 3969724127155030836783376764838284070891)) : ℚ) /
        ((((((((12 * 10^40
        + 7282106623272336454602866754327962638833) * 10^40
        + 1377420790216863537154272127020083035794) * 10^40
        + 12015972774141045254645495370760512934) * 10^40
        + 8210214958726809948987168364180295021109) * 10^40
        + 4667708982473657518817479378546497161060) * 10^40
        + 5282173329083556002822687618392331874204) * 10^40
        + 1179114696808872276555342284832176068445) * 10^40
        + 3284985159922568651615522665407356862464)))

noncomputable def neighborRightP026Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP026BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP026Center2557‖ ≤ neighborRightP026Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP026Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP026Input2557]
  have hs : compactExp2547 neighborRightP026Input2557 15 =
      (neighborRightP026Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP026Input2557 15).2 : ℝ) = neighborRightP026Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP026Error2557]
  have h := compactExp_error2547 neighborRightP026Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP026Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP026Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP026DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP026Factor2557 * embedPair2542 neighborRightP026Center2557‖ ≤
        (pairMagnitude2542 neighborRightP026Factor2557 : ℝ) * neighborRightP026Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP026Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP026Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP026BaseError2557
    (embedPair_magnitude2542 neighborRightP026Factor2557)

def neighborRightP027Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((52761707395609667092460043 : ℚ) /
        7378697629483820646400000000))

def neighborRightP027Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP027Factor2557 : RatPair2542 := ((((((((((((((31908458592579524617669757697072 *
    10^40
        + 9491205642021417020033960713844519462271) * 10^40
        + 6166683380786350988730469755715251977375) * 10^40
        + 7845495353550744965658571977285437721309) * 10^40
        + 8270398499862816033562163073499351559097) * 10^40
        + 9548927244769584294268179302534654062645) * 10^40
        + 2739859744977610458398709490628055774946) * 10^40
        + 620825949509106379341920572672346568151) * 10^40
        + 4024838342685565642852895088603389306058) * 10^40
        + 8358402397397314403855496829314724463607) * 10^40
        + 8402136442152950505819237618020716896072) * 10^40
        + 9323665367720594503603390787967865525829) : ℚ) /
        (((((((((((89555337355 * 10^40
        + 4738601391881683236606959501878973386764) * 10^40
        + 7446882965133697335052868671158867946502) * 10^40
        + 450655129206623105530524690610874796628) * 10^40
        + 2952422483709737834499545803314124373601) * 10^40
        + 3644266626431876831763122810452129083803) * 10^40
        + 6082858268790664551206539557148494539731) * 10^40
        + 6536751177709695192205944749348324419871) * 10^40
        + 9565097105880246083969093073580643160020) * 10^40
        + 4609242565480153022917943120200925543179) * 10^40
        + 8126617645019814746048848550143212829818) * 10^40
        + 8257406880565873859819297157720810979328)),
    (((-((((((((1162408605160361489 * 10^40
        + 2901882217089679222420176269634486417796) * 10^40
        + 9691685319357757805445236104730255338906) * 10^40
        + 2242967477918239409766166353110482335624) * 10^40
        + 7231132091272615369849808140770166243522) * 10^40
        + 4605917454594800504961345505824194514098) * 10^40
        + 2790396194276849634541618897022626263008) * 10^40
        + 7370315142227865269132049195082170241282) * 10^40
        + 3464914362453894633523648028963534590213)) : ℚ) /
        ((((((((101 * 10^40
        + 8256852986178691636822934034623701110665) * 10^40
        + 1019366321734908297234177016160664286352) * 10^40
        + 96127782193128362037163962966084103478) * 10^40
        + 5681719669814479591897346913442360168875) * 10^40
        + 7341671859789260150539835028371977288484) * 10^40
        + 2257386632668448022581500947138654993632) * 10^40
        + 9432917574470978212442738278657408547562) * 10^40
        + 6279881279380549212924181323258854899712)))

noncomputable def neighborRightP027Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP027BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP027Center2557‖ ≤ neighborRightP027Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP027Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP027Input2557]
  have hs : compactExp2547 neighborRightP027Input2557 15 =
      (neighborRightP027Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP027Input2557 15).2 : ℝ) = neighborRightP027Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP027Error2557]
  have h := compactExp_error2547 neighborRightP027Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP027Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP027Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP027DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP027Factor2557 * embedPair2542 neighborRightP027Center2557‖ ≤
        (pairMagnitude2542 neighborRightP027Factor2557 : ℝ) * neighborRightP027Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP027Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP027Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP027BaseError2557
    (embedPair_magnitude2542 neighborRightP027Factor2557)

def neighborRightP028Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((215061626496775559671970943 : ℚ) /
        29514790517935282585600000000))

def neighborRightP028Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP028Factor2557 : RatPair2542 := ((((((((((((((510535337474563406048317488440104 *
    10^40
        + 5150863203373743431303037452402798562693) * 10^40
        + 5749404115364035324907176682950804942499) * 10^40
        + 3444486580504823066529997505150709976349) * 10^40
        + 677819025714704375168125446954959818997) * 10^40
        + 9179249597307532676988227456450010728465) * 10^40
        + 4519472407761576819408122695141706247978) * 10^40
        + 7489810250501251608536666778044113371538) * 10^40
        + 427877451059035023523037897731803188478) * 10^40
        + 4711507574238002253387325438958944324233) * 10^40
        + 2047161275141719504932084949785812324098) * 10^40
        + 5627213118219052686822549685033170765869) : ℚ) /
        (((((((((((1432885397687 * 10^40
        + 5817622270106931785711352030063574188235) * 10^40
        + 9150127442139157360845898738541887144032) * 10^40
        + 7210482067305969688488395049773996746052) * 10^40
        + 7238759739355805351992732853025989977621) * 10^40
        + 8308266022910029308209964967234065340857) * 10^40
        + 7325732300650632819304632914375912635706) * 10^40
        + 4588018843355123075295115989573190717951) * 10^40
        + 3041553694083937343505489177290290560327) * 10^40
        + 3747881047682448366687089923214808690877) * 10^40
        + 25882320317035936781576802291405277101) * 10^40
        + 2118510089053981757108754523532975669248)),
    (((-((((((((75809369368534834572 * 10^40
        + 9061390572411185201230035730319917674479) * 10^40
        + 9302174542056491606790223011500170245532) * 10^40
        + 5228352771725392005694986910844118299160) * 10^40
        + 2113362154167703995956701059792876160487) * 10^40
        + 9329752924192365814079672946693880713298) * 10^40
        + 8767165533519229069067168394486421017063) * 10^40
        + 8968735522167360130665185311553218771593) * 10^40
        + 8261895712709247794562096226656130937753)) : ℚ) /
        ((((((((6516 * 10^40
        + 8438591115436264756667778215916871082566) * 10^40
        + 5239444591034131022987329034282514326528) * 10^40
        + 6152178060360215170378493629829382622628) * 10^40
        + 3630058868126693881430202460311050808046) * 10^40
        + 9866999026512649634549441815806546462990) * 10^40
        + 4472744490780673445216060616873919592508) * 10^40
        + 3706724766142605596335249834074147044008) * 10^40
        + 1912401880355149627147604688566713581568)))

noncomputable def neighborRightP028Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP028BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP028Center2557‖ ≤ neighborRightP028Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP028Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP028Input2557]
  have hs : compactExp2547 neighborRightP028Input2557 15 =
      (neighborRightP028Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP028Input2557 15).2 : ℝ) = neighborRightP028Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP028Error2557]
  have h := compactExp_error2547 neighborRightP028Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP028Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP028Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP028DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP028Factor2557 * embedPair2542 neighborRightP028Center2557‖ ≤
        (pairMagnitude2542 neighborRightP028Factor2557 : ℝ) * neighborRightP028Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP028Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP028Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP028BaseError2557
    (embedPair_magnitude2542 neighborRightP028Factor2557)

def neighborRightP029Input2557 : RatPair2542 := ((((-((578253 * 10^40
        + 2513856564207756821721200485072447507200) * 10^40
        + 2228388738134333030811403379672342761641)) : ℚ) /
        ((1043438 * 10^40
        + 5341836082217744690501668084214075543561) * 10^40
        + 3423907653835340883493847983718400000000)),
    ((221173897030652641300579731 : ℚ) /
        29514790517935282585600000000))

def neighborRightP029Center2557 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def neighborRightP029Factor2557 : RatPair2542 := ((((((((((((((510535337464106652649166592765903 *
    10^40
        + 128926907870161600656835846561500787770) * 10^40
        + 4078226799847247589577884352933283888911) * 10^40
        + 3786235256088623177521280843378079179936) * 10^40
        + 6993275511270139428069993478282772942983) * 10^40
        + 9175570783813884224276419930340852666877) * 10^40
        + 416013954478784545927538560799431360592) * 10^40
        + 3091903974069329357596177915753817549365) * 10^40
        + 1653317804597449268686234631880623779422) * 10^40
        + 746667134554426779783414787771059920560) * 10^40
        + 2027808565594761460437541441006065368808) * 10^40
        + 9262830674659585807872430541889398641013) : ℚ) /
        (((((((((((1432885397687 * 10^40
        + 5817622270106931785711352030063574188235) * 10^40
        + 9150127442139157360845898738541887144032) * 10^40
        + 7210482067305969688488395049773996746052) * 10^40
        + 7238759739355805351992732853025989977621) * 10^40
        + 8308266022910029308209964967234065340857) * 10^40
        + 7325732300650632819304632914375912635706) * 10^40
        + 4588018843355123075295115989573190717951) * 10^40
        + 3041553694083937343505489177290290560327) * 10^40
        + 3747881047682448366687089923214808690877) * 10^40
        + 25882320317035936781576802291405277101) * 10^40
        + 2118510089053981757108754523532975669248)),
    (((-((((((((77963948881825630971 * 10^40
        + 4050286365138385483064280244323636028564) * 10^40
        + 6921504659185219634577693208364522500280) * 10^40
        + 3765618532207052786893951414188448426525) * 10^40
        + 9029775372574100725763315252486116785946) * 10^40
        + 9142859128361245800541026973423186238300) * 10^40
        + 4903817431385325561140019124875451602554) * 10^40
        + 8885671502967982861480380856499035053624) * 10^40
        + 2923581079630063193380279729685420802733)) : ℚ) /
        ((((((((6516 * 10^40
        + 8438591115436264756667778215916871082566) * 10^40
        + 5239444591034131022987329034282514326528) * 10^40
        + 6152178060360215170378493629829382622628) * 10^40
        + 3630058868126693881430202460311050808046) * 10^40
        + 9866999026512649634549441815806546462990) * 10^40
        + 4472744490780673445216060616873919592508) * 10^40
        + 3706724766142605596335249834074147044008) * 10^40
        + 1912401880355149627147604688566713581568)))

noncomputable def neighborRightP029Error2557 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem neighborRightP029BaseError2557 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP029Center2557‖ ≤ neighborRightP029Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hz : ‖embedPair2542 neighborRightP029Input2557‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, neighborRightP029Input2557]
  have hs : compactExp2547 neighborRightP029Input2557 15 =
      (neighborRightP029Center2557, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 neighborRightP029Input2557 15).2 : ℝ) = neighborRightP029Error2557 :=
      by
    rw [hs]
    norm_num [neighborRightP029Error2557]
  have h := compactExp_error2547 neighborRightP029Input2557 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      neighborRightPosition2557 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          neighborRightP029Input2557) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [neighborRightPosition2557, storedWidth, nodeModulation2541,
      embedPair2542, neighborRightP029Input2557, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem neighborRightP029DerivativeError2557 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ neighborRightPosition2557 -
      embedPair2542 neighborRightP029Factor2557 * embedPair2542 neighborRightP029Center2557‖ ≤
        (pairMagnitude2542 neighborRightP029Factor2557 : ℝ) * neighborRightP029Error2557 := by
  have hx : |neighborRightPosition2557| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [neighborRightPosition2557, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) neighborRightPosition2557 = embedPair2542
          neighborRightP029Factor2557 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      neighborRightPosition2557, storedWidth, nodeModulation2541, embedPair2542,
      neighborRightP029Factor2557, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ neighborRightP029BaseError2557
    (embedPair_magnitude2542 neighborRightP029Factor2557)

theorem neighborRightGrid2557 :
    -stripRadius2303 + (2702 : ℝ) * (2 * stripRadius2303 / 10240) =
      neighborRightPosition2557 := by
  norm_num [stripRadius2303, neighborRightPosition2557]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.neighborRightP000DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP001DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP002DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP003DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP004DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP005DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP006DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP007DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP008DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP009DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP010DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP011DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP012DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP013DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP014DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP015DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP016DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP017DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP018DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP019DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP020DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP021DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP022DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP023DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP024DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP025DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP026DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP027DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP028DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightP029DerivativeError2557
#print axioms ConnesWeilRH.Dev.neighborRightGrid2557
