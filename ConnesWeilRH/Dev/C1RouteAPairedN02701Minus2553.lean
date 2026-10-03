import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def pairedN02701MinusPosition2553 : ℝ := (((-158531586419) : ℝ) /
        51200000000)

theorem pairedN02701MinusZero2553 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def pairedN02701MinusP000Center2553 : RatPair2542 := (0, 0)

def pairedN02701MinusP000Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02701MinusP000Error2553 : ℝ := 0

theorem pairedN02701MinusP000Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN02701MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |pairedN02701MinusPosition2553| := by
    norm_num [storedWidth, pairedN02701MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem pairedN02701MinusP000BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP000Center2553‖ ≤ pairedN02701MinusP000Error2553 := by
  rw [pairedN02701MinusP000Exterior2553]
  norm_num [pairedN02701MinusP000Center2553, pairedN02701MinusP000Error2553,
      pairedN02701MinusZero2553]

theorem pairedN02701MinusP000DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP000Factor2553 * embedPair2542
          pairedN02701MinusP000Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP000Factor2553 : ℝ) * pairedN02701MinusP000Error2553
            := by
  rw [pairedN02701MinusP000Exterior2553]
  norm_num [pairedN02701MinusP000Factor2553, pairedN02701MinusP000Center2553,
      pairedN02701MinusP000Error2553, pairedN02701MinusZero2553, pairMagnitude2542]

def pairedN02701MinusP001Input2553 : RatPair2542 := ((((-((334 * 10^40
        + 4181679957483969025469344287059963590135) * 10^40
        + 8161414014029282377368998074593359799021)) : ℚ) /
        ((941 * 10^40
        + 6102169216506454849034257242358098754684) * 10^40
        + 4000368461807982441421667880140800000000)),
    ((875774620147323865939848151 : ℚ) /
        3689348814741910323200000000))

def pairedN02701MinusP001Center2553 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP001Factor2553 : RatPair2542 := ((((((((((((((2808266803345 * 10^40
        + 5957100297016009635412644742900428893623) * 10^40
        + 8438153377917958291153209101156062822095) * 10^40
        + 7899405218859507970116023714182214070720) * 10^40
        + 213569205743468448505048291796779276768) * 10^40
        + 4360100342012592687887373167631305745203) * 10^40
        + 3741996590177405843157246273387480768074) * 10^40
        + 3884168208688822140325989481477239560459) * 10^40
        + 7311105641722298348567393383232065193026) * 10^40
        + 7060689937566886324557752505905061471399) * 10^40
        + 6479085544343026993371770560011221475742) * 10^40
        + 986900618183046977407968790076891160507) : ℚ) /
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
    (((-((((((((12346171 * 10^40
        + 7172528428377397174361962463679465917518) * 10^40
        + 134379022528133640469494256985146033833) * 10^40
        + 1745689415870294610147578449707590861404) * 10^40
        + 2168243389458206204120214599249239475072) * 10^40
        + 6475609588307538176899449374786494074852) * 10^40
        + 1593811312140055219546385205579636535244) * 10^40
        + 5715817545421899218419471183960068638274) * 10^40
        + 2058756612862421741778267269042308548843)) : ℚ) /
        (((((((2900242863486546972840900254409935003313 * 10^40
        + 2886911659530428454328810684955747709237) * 10^40
        + 2926949848572266501641263971861853851819) * 10^40
        + 3611042156476707720180651710753596486497) * 10^40
        + 2630002623515689516863840004131964275527) * 10^40
        + 4888409820754831583540978359385522341346) * 10^40
        + 3809565805659865221845538113057591023547) * 10^40
        + 5803898216573829710726339938742458908672)))

noncomputable def pairedN02701MinusP001Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP001BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP001Center2553‖ ≤ pairedN02701MinusP001Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP001Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP001Input2553]
  have hs : compactExp2547 pairedN02701MinusP001Input2553 9 =
      (pairedN02701MinusP001Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP001Input2553 9).2 : ℝ) =
      pairedN02701MinusP001Error2553
      := by
    rw [hs]
    norm_num [pairedN02701MinusP001Error2553]
  have h := compactExp_error2547 pairedN02701MinusP001Input2553 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          pairedN02701MinusP001Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP001Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP001DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP001Factor2553 * embedPair2542
          pairedN02701MinusP001Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP001Factor2553 : ℝ) * pairedN02701MinusP001Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP001Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP001Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP001BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP001Factor2553)

def pairedN02701MinusP002Input2553 : RatPair2542 := ((((-((8590 * 10^40
        + 1599478870791053102602381735213025077527) * 10^40
        + 4292607931183293216346445262371930612461)) : ℚ) /
        ((36680 * 10^40
        + 5267114824128922047222362789138794665314) * 10^40
        + 902751818529719531373343041126400000000)),
    (((-875774620147323865939848151) : ℚ) /
        1844674407370955161600000000))

def pairedN02701MinusP002Center2553 : RatPair2542 := ((((-7432742102829368094385) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-11177578774756275941739) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN02701MinusP002Factor2553 : RatPair2542 := ((((-(((((((((((383507034067793726147 * 10^40
        + 8935326509268907677719669012332423092351) * 10^40
        + 5106191213339222252939844823608321876929) * 10^40
        + 8631614032613092701568812620806117376660) * 10^40
        + 82151076697702263560566889572984116418) * 10^40
        + 8416511612952451132621765711831505289231) * 10^40
        + 952262457884278468995531170230725227747) * 10^40
        + 7127033268064112794538549263730068476402) * 10^40
        + 6863480642474610426927934054489878758141) * 10^40
        + 6087071441204588260156938916290656821762) * 10^40
        + 8711616840497437328833151544737598180291) * 10^40
        + 3836023725169601044984409524748372844613)) : ℚ) /
        (((((((((((2973195288712711 * 10^40
        + 3467491001347320719026811728854004467225) * 10^40
        + 1497422596870896662502961256242652510112) * 10^40
        + 7123366041167959743416343679381071886563) * 10^40
        + 6351689116260193294883773403656430093094) * 10^40
        + 8536920865766590409249653040015133419775) * 10^40
        + 6759648893826305400074757333793637280579) * 10^40
        + 3370348402296274339099910999518804386499) * 10^40
        + 4450536458668312164611614967167537131595) * 10^40
        + 5851976647608324881727935799688345485937) * 10^40
        + 1144248433032258675358557443885865002559) * 10^40
        + 9746374910327650698446513022155786027008)),
    ((((((((((1402759776363 * 10^40
        + 1488403154402126893030666618668186085423) * 10^40
        + 2946954655321923273172471226892265744126) * 10^40
        + 6949888140188414088888372870833707755291) * 10^40
        + 4985274473603261424710906929485641094260) * 10^40
        + 3505101716444404625860794958635848765199) * 10^40
        + 9532135581032387576413443716256620856878) * 10^40
        + 5132756994283538195443491183814702403699) * 10^40
        + 228746068361200375132460350013086271723) : ℚ) /
        ((((((((10685920 * 10^40
        + 8698626573180637225289470245261943687371) * 10^40
        + 4854664925507741346767746110602685453773) * 10^40
        + 8948137748171180319286033348791544416498) * 10^40
        + 45943021343597819906620002252686948939) * 10^40
        + 2695148327310254383957658387883810823093) * 10^40
        + 3423061642949699721752439843960503724256) * 10^40
        + 5759831459438283503857105702531114993435) * 10^40
        + 1798758157118995008057425425787038728192)))

noncomputable def pairedN02701MinusP002Error2553 : ℝ := ((49382499124458385033 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP002BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP002Center2553‖ ≤ pairedN02701MinusP002Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP002Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP002Input2553]
  have hs : compactExp2547 pairedN02701MinusP002Input2553 8 =
      (pairedN02701MinusP002Center2553, ((49382499124458385033 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP002Input2553 8).2 : ℝ) =
      pairedN02701MinusP002Error2553
      := by
    rw [hs]
    norm_num [pairedN02701MinusP002Error2553]
  have h := compactExp_error2547 pairedN02701MinusP002Input2553 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          pairedN02701MinusP002Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP002Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP002DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP002Factor2553 * embedPair2542
          pairedN02701MinusP002Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP002Factor2553 : ℝ) * pairedN02701MinusP002Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP002Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP002Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP002BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP002Factor2553)

def pairedN02701MinusP003Input2553 : RatPair2542 := ((((-((1123649 * 10^40
        + 8976927238487000191863367108472502773987) * 10^40
        + 3331593634587051799526484294029501456047)) : ℚ) /
        ((6644764 * 10^40
        + 348595898346936727630550565694213304645) * 10^40
        + 356964576015918677191939509452800000000)),
    (((-875774620147323865939848151) : ℚ) /
        1844674407370955161600000000))

def pairedN02701MinusP003Center2553 : RatPair2542 := ((((-128031342998015805707829314715) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-192537343849641036358254016761) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN02701MinusP003Factor2553 : RatPair2542 :=
    ((((-(((((((((((175368114919220931111472481097235144 *
    10^40
        + 932793480979086925649357932287953691922) * 10^40
        + 9600725802266248326954609159234671283053) * 10^40
        + 1343931023334109361646739019919383613589) * 10^40
        + 1704211818250786945061335868012241910037) * 10^40
        + 6027454371950573315120440519349219653131) * 10^40
        + 2427018930870527141789544124404020173055) * 10^40
        + 1967099911737326817964094021320699172598) * 10^40
        + 7088773115481261682416029589845218563453) * 10^40
        + 5444994395511691182204049846542264214149) * 10^40
        + 2171359560667520808845332883438753123083) * 10^40
        + 3546136336548777654491511889183707916639)) : ℚ) /
        (((((((((((2836946849426626479149101344661 * 10^40
        + 6848653026526952473608279496525788854436) * 10^40
        + 3964585963216090121549265271518849615527) * 10^40
        + 3582261462027080272810322374778004100368) * 10^40
        + 7142106839950723621973559926596014676354) * 10^40
        + 9702445030132414072552602738474297875371) * 10^40
        + 562215862901001402963229486963477988272) * 10^40
        + 3069196005786681873393366004557209310497) * 10^40
        + 287182526806631665199914693007782041390) * 10^40
        + 650136070536019920135500131706419141180) * 10^40
        + 2877838113113495729198507663286273944508) * 10^40
        + 2169628627894784569057348383497282125824)),
    (((-((((((((1366867566593460312427 * 10^40
        + 3867487640407552112289527882401058481417) * 10^40
        + 6424813776036267558537668999406052578413) * 10^40
        + 1706733754928054129008911435002945176518) * 10^40
        + 3553495462308948088065032334844478926408) * 10^40
        + 3124127680596889016493189447687814444123) * 10^40
        + 2131966844065103658256953511427067984063) * 10^40
        + 5072966019352269751472529585174395372985) * 10^40
        + 8049205644015529135275879348784235782671)) : ℚ) /
        ((((((((34523054038309545 * 10^40
        + 8070460829836846567823988656416628066383) * 10^40
        + 4587402166612519557745250159747618326596) * 10^40
        + 7613747391599567274633108774437485695163) * 10^40
        + 9343961057035675497914777333331863985921) * 10^40
        + 4482676832355296082588408153974825262161) * 10^40
        + 2992432219252968330401935066320003582024) * 10^40
        + 1817157221406445207864595536940876164476) * 10^40
        + 3970392011049662611515175051787780489216)))

noncomputable def pairedN02701MinusP003Error2553 : ℝ := ((797028780675931752600253645 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP003BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP003Center2553‖ ≤ pairedN02701MinusP003Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP003Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP003Input2553]
  have hs : compactExp2547 pairedN02701MinusP003Input2553 8 =
      (pairedN02701MinusP003Center2553, ((797028780675931752600253645 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP003Input2553 8).2 : ℝ) =
      pairedN02701MinusP003Error2553
      := by
    rw [hs]
    norm_num [pairedN02701MinusP003Error2553]
  have h := compactExp_error2547 pairedN02701MinusP003Input2553 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          pairedN02701MinusP003Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP003Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP003DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP003Factor2553 * embedPair2542
          pairedN02701MinusP003Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP003Factor2553 : ℝ) * pairedN02701MinusP003Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP003Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP003Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP003BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP003Factor2553)

def pairedN02701MinusP004Input2553 : RatPair2542 := ((((-((19409 * 10^40
        + 4221726842157504765492452247847422161138) * 10^40
        + 1088311962520617223323074241864118112461)) : ℚ) /
        ((134028 * 10^40
        + 5763226050861645114137505055527745988340) * 10^40
        + 4359916327702839531373343041126400000000)),
    ((875774620147323865939848151 : ℚ) /
        1844674407370955161600000000))

def pairedN02701MinusP004Center2553 : RatPair2542 := ((((-64207546511769766768481979511471) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((96557219279266825819155349428839 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN02701MinusP004Factor2553 : RatPair2542 := ((((-(((((((((((216694693276026834209932 *
    10^40
        + 1307423185770032169917036799131893584982) * 10^40
        + 6842145214454184666811193747672928549484) * 10^40
        + 4480536895631130480735048877626469610966) * 10^40
        + 2397104180552631853434489296792774790428) * 10^40
        + 5117049261533099538664569460076922549512) * 10^40
        + 8981362610729022880642924608661417028380) * 10^40
        + 3040180194264909723056726890825686123849) * 10^40
        + 6023957098744764946252230781560654955203) * 10^40
        + 6302510693512765089138539520249438774601) * 10^40
        + 5177030766952426693974342012316712378584) * 10^40
        + 2441723983328434041202582229826497844613)) : ℚ) /
        (((((((((((7076108494268236128 * 10^40
        + 5512677350823931577586294426013899536395) * 10^40
        + 4357331986955214189831752749644446998030) * 10^40
        + 3453672177138996097392199696737016040068) * 10^40
        + 6909595796835627650361600573614412289870) * 10^40
        + 236090150558416317605782724320061633202) * 10^40
        + 6083210652550920013361236792774687549096) * 10^40
        + 1125954276444360917807836159006829580198) * 10^40
        + 1264992542678426658319358638486322935958) * 10^40
        + 6377372885200927084687617681447509142226) * 10^40
        + 4823479753613738961837244945395720839239) * 10^40
        + 373393981726415203124913022155786027008)),
    ((((((((((106342771197799 * 10^40
        + 2983832374188722391176392620740282004345) * 10^40
        + 8088304632948529055042001700888371981745) * 10^40
        + 2943664965665298624095409027457042241910) * 10^40
        + 3515737296263345259108860698038279598012) * 10^40
        + 745580670828077234843742698067743421363) * 10^40
        + 7980327582243985494187685828699702735615) * 10^40
        + 454492526094373181909603379870231114242) * 10^40
        + 8883901938894639516332306349205663728277) : ℚ) /
        ((((((((1904843580 * 10^40
        + 4824523594531213353034759566469063183137) * 10^40
        + 9203733929667876279931105266675600147748) * 10^40
        + 5546782268739206171043400601465671486465) * 10^40
        + 9000377039929565390305917709883691541199) * 10^40
        + 9386594298950469050406216961415163469388) * 10^40
        + 2757914341002766027590561291455103603396) * 10^40
        + 3989138872955181030968949404074575480103) * 10^40
        + 6185754302836897738911825425787038728192)))

noncomputable def pairedN02701MinusP004Error2553 : ℝ := ((97529468585144800089090291783 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem pairedN02701MinusP004BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP004Center2553‖ ≤ pairedN02701MinusP004Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP004Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP004Input2553]
  have hs : compactExp2547 pairedN02701MinusP004Input2553 8 =
      (pairedN02701MinusP004Center2553, ((97529468585144800089090291783 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP004Input2553 8).2 : ℝ) =
      pairedN02701MinusP004Error2553
      := by
    rw [hs]
    norm_num [pairedN02701MinusP004Error2553]
  have h := compactExp_error2547 pairedN02701MinusP004Input2553 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          pairedN02701MinusP004Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP004Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP004DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP004Factor2553 * embedPair2542
          pairedN02701MinusP004Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP004Factor2553 : ℝ) * pairedN02701MinusP004Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP004Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP004Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP004BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP004Factor2553)

def pairedN02701MinusP005Center2553 : RatPair2542 := (0, 0)

def pairedN02701MinusP005Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02701MinusP005Error2553 : ℝ := 0

theorem pairedN02701MinusP005Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN02701MinusPosition2553 =
        0
        := by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |pairedN02701MinusPosition2553| := by
    norm_num [storedWidth, pairedN02701MinusPosition2553]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem pairedN02701MinusP005BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP005Center2553‖ ≤ pairedN02701MinusP005Error2553 := by
  rw [pairedN02701MinusP005Exterior2553]
  norm_num [pairedN02701MinusP005Center2553, pairedN02701MinusP005Error2553,
      pairedN02701MinusZero2553]

theorem pairedN02701MinusP005DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP005Factor2553 * embedPair2542
          pairedN02701MinusP005Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP005Factor2553 : ℝ) * pairedN02701MinusP005Error2553
            := by
  rw [pairedN02701MinusP005Exterior2553]
  norm_num [pairedN02701MinusP005Factor2553, pairedN02701MinusP005Center2553,
      pairedN02701MinusP005Error2553, pairedN02701MinusZero2553, pairMagnitude2542]

def pairedN02701MinusP006Input2553 : RatPair2542 := ((((-42061326624915781747488640051599353) : ℚ)
    /
        73447401531966028759865753600000000),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP006Center2553 : RatPair2542 := (((21384329496406693 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP006Factor2553 : RatPair2542 := ((((((2242240781371404900 * 10^40
        + 8530548551000458124401099423136141519172) * 10^40
        + 5943969153190212800004851247723804860573) * 10^40
        + 839387566255348826134285345536541115357) : ℚ) /
        (((6687330808176 * 10^40
        + 6002578591449565797216574011898289303650) * 10^40
        + 3939425513291405934887286533123709590768) * 10^40
        + 9399380879513689390925717235707671077144)),
    ((0 : ℚ) /
        1))

noncomputable def pairedN02701MinusP006Error2553 : ℝ := ((3767500786445 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem pairedN02701MinusP006BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP006Center2553‖ ≤ pairedN02701MinusP006Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP006Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP006Input2553]
  have hs : compactExp2547 pairedN02701MinusP006Input2553 7 =
      (pairedN02701MinusP006Center2553, ((3767500786445 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP006Input2553 7).2 : ℝ) =
      pairedN02701MinusP006Error2553
      := by
    rw [hs]
    norm_num [pairedN02701MinusP006Error2553]
  have h := compactExp_error2547 pairedN02701MinusP006Input2553 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          pairedN02701MinusP006Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP006Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP006DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP006Factor2553 * embedPair2542
          pairedN02701MinusP006Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP006Factor2553 : ℝ) * pairedN02701MinusP006Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP006Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP006Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP006BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP006Factor2553)

def pairedN02701MinusP007Input2553 : RatPair2542 := ((((-((1123649 * 10^40
        + 8976927238487000191863367108472502773987) * 10^40
        + 3331593634587051799526484294029501456047)) : ℚ) /
        ((1661191 * 10^40
        + 87148974586734181907637641423553326161) * 10^40
        + 2589241144003979669297984877363200000000)),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP007Center2553 : RatPair2542 := (((231219924674649256075727664923 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP007Factor2553 : RatPair2542 := ((((((((((((((1196642 * 10^40
        + 7584933192257659562695220255537513332371) * 10^40
        + 8564651576196390738705079835767546904911) * 10^40
        + 4785238035655265000781440787557321154262) * 10^40
        + 410678581597194668318922448842051122608) * 10^40
        + 8059239011574412421629550152315313411498) * 10^40
        + 6071753596475006262314276850290804049488) * 10^40
        + 8600972500689294199187423960176393755234) * 10^40
        + 7177455877578514280281897067957781503064) * 10^40
        + 3442805759077293422899399461821567101309) * 10^40
        + 6878360822660292314322172937553225367255) * 10^40
        + 2739981005496095892073438759218558379757) : ℚ) /
        (((((((((((572 * 10^40
        + 9168536838620263647789327365163239328663) * 10^40
        + 2895968366057837266590791447972347641357) * 10^40
        + 388847158189239547487429407815172457043) * 10^40
        + 4322102071344416543377357220546303422128) * 10^40
        + 3230948997357320117474221517091287190934) * 10^40
        + 2113418934734069016122527542713173515449) * 10^40
        + 7310218525138985687235511362740514339269) * 10^40
        + 1681378273361344586123753549818662439393) * 10^40
        + 6532984085502177972160514255399333333880) * 10^40
        + 8999217342116647965692421315222231142313) * 10^40
        + 3768599956031232863412489926251532961944)),
    ((0 : ℚ) /
        1))

noncomputable def pairedN02701MinusP007Error2553 : ℝ := ((16000632657409328590635391 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem pairedN02701MinusP007BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP007Center2553‖ ≤ pairedN02701MinusP007Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP007Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP007Input2553]
  have hs : compactExp2547 pairedN02701MinusP007Input2553 6 =
      (pairedN02701MinusP007Center2553, ((16000632657409328590635391 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP007Input2553 6).2 : ℝ) =
      pairedN02701MinusP007Error2553
      := by
    rw [hs]
    norm_num [pairedN02701MinusP007Error2553]
  have h := compactExp_error2547 pairedN02701MinusP007Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN02701MinusP007Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP007Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP007DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP007Factor2553 * embedPair2542
          pairedN02701MinusP007Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP007Factor2553 : ℝ) * pairedN02701MinusP007Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP007Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP007Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP007BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP007Factor2553)

def pairedN02701MinusP008Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((630729240492097551551105443 : ℚ) /
        944473296573929042739200000000))

def pairedN02701MinusP008Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP008Factor2553 : RatPair2542 :=
    ((((((((((((((1211859898566857367192002436746835 * 10^40
        + 687489676936055357139146985520481225255) * 10^40
        + 4106296245044853036692460452410419882326) * 10^40
        + 8410630551377881262440089763242534630372) * 10^40
        + 5644015828316796756579354689681488939600) * 10^40
        + 8257187625161637245554064245177211341307) * 10^40
        + 89447055943092285365772576557465851411) * 10^40
        + 4578188590192124489104488019324428205183) * 10^40
        + 7642330180083958232976882851296406164498) * 10^40
        + 7676450441210741637166568564015064334925) * 10^40
        + 5639107446110990633696391786781922809669) * 10^40
        + 4672185237779347409681669937008825587449) : ℚ) /
        (((((((((((53129793661 * 10^40
        + 5007451626948456301876121112323343007501) * 10^40
        + 512428949947293647684309779051055632558) * 10^40
        + 3561519778664584485439540055036606060567) * 10^40
        + 6422023018802656676695857449214012221958) * 10^40
        + 1971887503150481071080849994614806617847) * 10^40
        + 9669590323677850331503446168191500095675) * 10^40
        + 3318328283880346364296218309535025541087) * 10^40
        + 8954004992439027999484510221645373434579) * 10^40
        + 2569809118918598516902226407843275360822) * 10^40
        + 9822688843753239179488975125859477006478) * 10^40
        + 4020223630462649060065553533989128503296)),
    (((-((((((((263628623880208465126 * 10^40
        + 9044156624049637899031005252600127442421) * 10^40
        + 8224827630753197795616955185302496358651) * 10^40
        + 4783762207671677820671779301024012304968) * 10^40
        + 7264058502886942438428837781703607971298) * 10^40
        + 1325303980779672599487659205868710959988) * 10^40
        + 1213724515368741737283427269982496428399) * 10^40
        + 3343699115338377074496609197024214222805) * 10^40
        + 8587201192108120705859574020854864849693)) : ℚ) /
        ((((((((7729 * 10^40
        + 4837318072590597840552870501097756850724) * 10^40
        + 4781501533621654299657649497215044513448) * 10^40
        + 9563377623048415760176099549591302788187) * 10^40
        + 1000664459254159763726137558544413714928) * 10^40
        + 8372752059637550852644505599220433275192) * 10^40
        + 3343940703284548809449863170981759854536) * 10^40
        + 5017529300504592352749711117348899791699) * 10^40
        + 4807389080660183792171320414302243913728)))

noncomputable def pairedN02701MinusP008Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP008BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP008Center2553‖ ≤ pairedN02701MinusP008Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP008Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP008Input2553]
  have hs : compactExp2547 pairedN02701MinusP008Input2553 16 =
      (pairedN02701MinusP008Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP008Input2553 16).2 : ℝ) =
      pairedN02701MinusP008Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP008Error2553]
  have h := compactExp_error2547 pairedN02701MinusP008Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP008Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP008Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP008DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP008Factor2553 * embedPair2542
          pairedN02701MinusP008Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP008Factor2553 : ℝ) * pairedN02701MinusP008Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP008Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP008Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP008BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP008Factor2553)

def pairedN02701MinusP009Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((938059634128117561826070909 : ℚ) /
        944473296573929042739200000000))

def pairedN02701MinusP009Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP009Factor2553 : RatPair2542 :=
    ((((((((((((((1211859898565762788745141158529397 * 10^40
        + 6161076585187717021888713591989291485539) * 10^40
        + 436928271789230954511309969033093098805) * 10^40
        + 1583804789741273085602567596024700060702) * 10^40
        + 1371231044615852224822686452207573082960) * 10^40
        + 1325899769109854149830251523716638765018) * 10^40
        + 5033521127047691901043445731143467747474) * 10^40
        + 5133147944783005870098281453280887463061) * 10^40
        + 2310563248782633572280954369139626420096) * 10^40
        + 4520932293017941647532767110301865458878) * 10^40
        + 4648429455207989714223398377825456273780) * 10^40
        + 6498790565129347887696510643462384675897) : ℚ) /
        (((((((((((53129793661 * 10^40
        + 5007451626948456301876121112323343007501) * 10^40
        + 512428949947293647684309779051055632558) * 10^40
        + 3561519778664584485439540055036606060567) * 10^40
        + 6422023018802656676695857449214012221958) * 10^40
        + 1971887503150481071080849994614806617847) * 10^40
        + 9669590323677850331503446168191500095675) * 10^40
        + 3318328283880346364296218309535025541087) * 10^40
        + 8954004992439027999484510221645373434579) * 10^40
        + 2569809118918598516902226407843275360822) * 10^40
        + 9822688843753239179488975125859477006478) * 10^40
        + 4020223630462649060065553533989128503296)),
    (((-((((((((130694945145188166588 * 10^40
        + 3564990989427284181036821617295069487661) * 10^40
        + 3323942596647779400323418816553392182301) * 10^40
        + 3394837279364056392777510163829149765096) * 10^40
        + 8071310318857558227306844317286303618388) * 10^40
        + 9141815957774780485966503832378303920275) * 10^40
        + 6133701570015727059114124870046021417490) * 10^40
        + 6018947608150590617069349063117776072698) * 10^40
        + 7655305205256115699238166213910582774401)) : ℚ) /
        ((((((((2576 * 10^40
        + 4945772690863532613517623500365918950241) * 10^40
        + 4927167177873884766552549832405014837816) * 10^40
        + 3187792541016138586725366516530434262729) * 10^40
        + 333554819751386587908712519514804571642) * 10^40
        + 9457584019879183617548168533073477758397) * 10^40
        + 4447980234428182936483287723660586618178) * 10^40
        + 8339176433501530784249903705782966597233) * 10^40
        + 1602463026886727930723773471434081304576)))

noncomputable def pairedN02701MinusP009Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP009BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP009Center2553‖ ≤ pairedN02701MinusP009Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP009Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP009Input2553]
  have hs : compactExp2547 pairedN02701MinusP009Input2553 16 =
      (pairedN02701MinusP009Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP009Input2553 16).2 : ℝ) =
      pairedN02701MinusP009Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP009Error2553]
  have h := compactExp_error2547 pairedN02701MinusP009Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP009Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP009Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP009DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN02701MinusPosition2553 -
      embedPair2542 pairedN02701MinusP009Factor2553 * embedPair2542
          pairedN02701MinusP009Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP009Factor2553 : ℝ) * pairedN02701MinusP009Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP009Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP009Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP009BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP009Factor2553)

def pairedN02701MinusP010Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((558025679572758329216722299 : ℚ) /
        472236648286964521369600000000))

def pairedN02701MinusP010Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP010Factor2553 : RatPair2542 :=
    ((((((((((((((302964974641233186433020323493550
    * 10^40
        + 2859970354545423515407960715532812443735) * 10^40
        + 9485760178427596060241854943415148208981) * 10^40
        + 7175973290468918319307438756425103097433) * 10^40
        + 7375265952392667606263060389953107476083) * 10^40
        + 5104273449379418422162933916347120648781) * 10^40
        + 7730944738981156878695044152448174670876) * 10^40
        + 9873408661623186994623140118632482565872) * 10^40
        + 70751635739615268007389010363229167070) * 10^40
        + 7185946917112316178939364415418835632372) * 10^40
        + 8115282409760792808703938235748344973274) * 10^40
        + 760265171287063464922541249712256530761) : ℚ) /
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
    (((-((((((((19436700218197886547 * 10^40
        + 5941093990812844957407340618457499820416) * 10^40
        + 6544434584698665616845783206879235129556) * 10^40
        + 6584104819840170554407814133227018952389) * 10^40
        + 8682030536790761098321706951646257966505) * 10^40
        + 8105972815103301688282384679121206639410) * 10^40
        + 1532495543439549212705198621235192142981) * 10^40
        + 7906495146117838101108628458516577493281) * 10^40
        + 4310157568392296387950795756280718180807)) : ℚ) /
        ((((((((322 * 10^40
        + 618221586357941576689702937545739868780) * 10^40
        + 1865895897234235595819068729050626854727) * 10^40
        + 398474067627017323340670814566304282841) * 10^40
        + 1291694352468923323488589064939350571455) * 10^40
        + 3682198002484897952193521066634184719799) * 10^40
        + 6805997529303522867060410965457573327272) * 10^40
        + 3542397054187691348031237963222870824654) * 10^40
        + 1450307878360840991340471683929260163072)))

noncomputable def pairedN02701MinusP010Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP010BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP010Center2553‖ ≤ pairedN02701MinusP010Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP010Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP010Input2553]
  have hs : compactExp2547 pairedN02701MinusP010Input2553 16 =
      (pairedN02701MinusP010Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP010Input2553 16).2 : ℝ) =
      pairedN02701MinusP010Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP010Error2553]
  have h := compactExp_error2547 pairedN02701MinusP010Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP010Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP010Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP010DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP010Factor2553 * embedPair2542
          pairedN02701MinusP010Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP010Factor2553 : ℝ) * pairedN02701MinusP010Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP010Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP010Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP010BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP010Factor2553)

def pairedN02701MinusP011Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((617361885721254929729880619 : ℚ) /
        472236648286964521369600000000))

def pairedN02701MinusP011Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP011Factor2553 : RatPair2542 :=
    ((((((((((((((302964974641074851134199089161511
    * 10^40
        + 2163561835568444774000542207489837429879) * 10^40
        + 8784021840894168753790706768649062640114) * 10^40
        + 451032006721322342198685366747555643733) * 10^40
        + 3001262570335758077240149785337074748510) * 10^40
        + 6263151966748259916530256689379636333196) * 10^40
        + 2882481672509123145711349623505492857960) * 10^40
        + 1293560209029729928627091326434806237258) * 10^40
        + 3215215363474821051695484868331234223091) * 10^40
        + 9586126689455437368169560412760076191745) * 10^40
        + 6872687387745810724858991993696082504513) * 10^40
        + 512094618620488965014078444753862359401) : ℚ) /
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
    (((-((((((((64510353222947632293 * 10^40
        + 1155684962721924727979651470353835624994) * 10^40
        + 9113198002511207057374747216550431588860) * 10^40
        + 151896283697583762350016592064877035879) * 10^40
        + 6551029491561809705949538826802596903558) * 10^40
        + 3311128370016095820919142188373100038790) * 10^40
        + 1439956751636964362344598052615992278684) * 10^40
        + 410777342958252443293689865887490981773) * 10^40
        + 8597954277690333147974120188342589060421)) : ℚ) /
        ((((((((966 * 10^40
        + 1854664759073824730069108812637219606340) * 10^40
        + 5597687691702706787457206187151880564181) * 10^40
        + 1195422202881051970022012443698912848523) * 10^40
        + 3875083057406769970465767194818051714366) * 10^40
        + 1046594007454693856580563199902554159399) * 10^40
        + 417992587910568601181232896372719981817) * 10^40
        + 627191162563074044093713889668612473962) * 10^40
        + 4350923635082522974021415051787780489216)))

noncomputable def pairedN02701MinusP011Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP011BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP011Center2553‖ ≤ pairedN02701MinusP011Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP011Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP011Input2553]
  have hs : compactExp2547 pairedN02701MinusP011Input2553 16 =
      (pairedN02701MinusP011Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP011Input2553 16).2 : ℝ) =
      pairedN02701MinusP011Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP011Error2553]
  have h := compactExp_error2547 pairedN02701MinusP011Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP011Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP011Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP011DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP011Factor2553 * embedPair2542
          pairedN02701MinusP011Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP011Factor2553 : ℝ) * pairedN02701MinusP011Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP011Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP011Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP011BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP011Factor2553)

def pairedN02701MinusP012Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((13576393469632358173878271 : ℚ) /
        9444732965739290427392000000))

def pairedN02701MinusP012Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP012Factor2553 : RatPair2542 :=
    ((((((((((((((75741243660223500166125361799988
    * 10^40
        + 9309399034362930990590023749178053455884) * 10^40
        + 5486363841785719000437510528372160371558) * 10^40
        + 1099596189293374971355372040733154892753) * 10^40
        + 5991110601185754064755486921655697487912) * 10^40
        + 4085730222489480742071669013674962169846) * 10^40
        + 9086618406396380440185355279654012720500) * 10^40
        + 1402747167103806392966203963146326699752) * 10^40
        + 7370278697068897971550467856322284979640) * 10^40
        + 9669873683027277527329364128492374728576) * 10^40
        + 6540906321898869218737099518306706207942) * 10^40
        + 2584186846958438322601722662676139964193) : ℚ) /
        (((((((((((3320612103 * 10^40
        + 8437965726684278518867257569520208937968) * 10^40
        + 8157026809371705852980269361190690977034) * 10^40
        + 8972594986166536530339971253439787878785) * 10^40
        + 4776376438675166042293491090575875763872) * 10^40
        + 3873242968946905066942553124663425413615) * 10^40
        + 4979349395229865645718965385511968755979) * 10^40
        + 7082395517742521647768513644345939096317) * 10^40
        + 9934625312027439249967781888852835839661) * 10^40
        + 2035613069932412407306389150490204710051) * 10^40
        + 4363918052734577448718060945366217312904) * 10^40
        + 9001263976903915566254097095874320531456)),
    (((-((((((((8866537180988662728 * 10^40
        + 4445149520869069759057552177299526986199) * 10^40
        + 5541237265204222728054038581709489551319) * 10^40
        + 3154207431613500954659321477095933435960) * 10^40
        + 2768066764432262367148318137117774584408) * 10^40
        + 4742645108711077926322554050001387757537) * 10^40
        + 9433003456270898970883794035545707021924) * 10^40
        + 7019025196472194265690883937557790257738) * 10^40
        + 9296014393125936877412786006291037780225)) : ℚ) /
        ((((((((120 * 10^40
        + 7731833094884228091258638601579652450792) * 10^40
        + 5699710961462838348432150773393985070522) * 10^40
        + 6399427775360131496252751555462364106065) * 10^40
        + 4234385382175846246308220899352256464295) * 10^40
        + 7630824250931836732072570399987819269924) * 10^40
        + 8802249073488821075147654112046589997727) * 10^40
        + 1328398895320384255511714236208576559245) * 10^40
        + 3043865454385315371752676881473472561152)))

noncomputable def pairedN02701MinusP012Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP012BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP012Center2553‖ ≤ pairedN02701MinusP012Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP012Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP012Input2553]
  have hs : compactExp2547 pairedN02701MinusP012Input2553 16 =
      (pairedN02701MinusP012Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP012Input2553 16).2 : ℝ) =
      pairedN02701MinusP012Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP012Error2553]
  have h := compactExp_error2547 pairedN02701MinusP012Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP012Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP012Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP012DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP012Factor2553 * embedPair2542
          pairedN02701MinusP012Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP012Factor2553 : ℝ) * pairedN02701MinusP012Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP012Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP012Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP012BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP012Factor2553)

def pairedN02701MinusP013Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((146965053600227290725850929 : ℚ) /
        94447329657392904273920000000))

def pairedN02701MinusP013Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP013Factor2553 : RatPair2542 :=
    ((((((((((((((302964974640714259051581743814689
    * 10^40
        + 5714605649873613957758160723322342086644) * 10^40
        + 2367696154831745540045889971904365201314) * 10^40
        + 4690541639088952837061136600658144759896) * 10^40
        + 5377295868617709563900152644972655802222) * 10^40
        + 8652158074989984156371596449600695901553) * 10^40
        + 4608350437115325643491497547519078450299) * 10^40
        + 7770606234674139157038755994622423577502) * 10^40
        + 7661321422227026082782904240590691038535) * 10^40
        + 4339658347364352320539259010988052218837) * 10^40
        + 3802015670164024689449460900498690708700) * 10^40
        + 6340778927782667166208911184907804195497) : ℚ) /
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
    (((-((((((((25594840828521501100 * 10^40
        + 1384380866397748435377801427195971085719) * 10^40
        + 7582045127858535228246053167052832077248) * 10^40
        + 1677597904774699292667599816705861170380) * 10^40
        + 5827979790292582436854781336797572639612) * 10^40
        + 4953816692010696922861636070286245095199) * 10^40
        + 6197700252048617148422283023410027769344) * 10^40
        + 5820729099076559948340912986364274692119) * 10^40
        + 9029859146209480304978940833400972325065)) : ℚ) /
        ((((((((322 * 10^40
        + 618221586357941576689702937545739868780) * 10^40
        + 1865895897234235595819068729050626854727) * 10^40
        + 398474067627017323340670814566304282841) * 10^40
        + 1291694352468923323488589064939350571455) * 10^40
        + 3682198002484897952193521066634184719799) * 10^40
        + 6805997529303522867060410965457573327272) * 10^40
        + 3542397054187691348031237963222870824654) * 10^40
        + 1450307878360840991340471683929260163072)))

noncomputable def pairedN02701MinusP013Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP013BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP013Center2553‖ ≤ pairedN02701MinusP013Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP013Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP013Input2553]
  have hs : compactExp2547 pairedN02701MinusP013Input2553 16 =
      (pairedN02701MinusP013Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP013Input2553 16).2 : ℝ) =
      pairedN02701MinusP013Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP013Error2553]
  have h := compactExp_error2547 pairedN02701MinusP013Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP013Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP013Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP013DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP013Factor2553 * embedPair2542
          pairedN02701MinusP013Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP013Factor2553 : ℝ) * pairedN02701MinusP013Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP013Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP013Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP013BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP013Factor2553)

def pairedN02701MinusP014Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((838597898629083505249081609 : ℚ) /
        472236648286964521369600000000))

def pairedN02701MinusP014Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP014Factor2553 : RatPair2542 :=
    ((((((((((((((302964974640343573852360388873580
    * 10^40
        + 8657837319111233570141797917641482702554) * 10^40
        + 2452511027322700411103692420174743545163) * 10^40
        + 1784348447310330471650029435625457563467) * 10^40
        + 4242632021087715841502031579264423843177) * 10^40
        + 4993186851144267135722763957100934147346) * 10^40
        + 6783289562986914916063075794218973624596) * 10^40
        + 8126487662473406165757589603637259359797) * 10^40
        + 5888482902062104268155313795585692515821) * 10^40
        + 2718628571842850362831747836792781989766) * 10^40
        + 1907006369478024323698067832746324335309) * 10^40
        + 6679935949338931073718138138089419444481) : ℚ) /
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
    (((-((((((((87628096103417698802 * 10^40
        + 9052431926793578394217511407886007064252) * 10^40
        + 6306099734828092535724409216699766497419) * 10^40
        + 4385840899807347021194349134703384949419) * 10^40
        + 1712783712913465422677006892119190991350) * 10^40
        + 7382609301972198750386677924526324549672) * 10^40
        + 4296024476355723772149913558721025005078) * 10^40
        + 3900384240242401785582855505398711360056) * 10^40
        + 3534934795550089948293605922241172177071)) : ℚ) /
        ((((((((966 * 10^40
        + 1854664759073824730069108812637219606340) * 10^40
        + 5597687691702706787457206187151880564181) * 10^40
        + 1195422202881051970022012443698912848523) * 10^40
        + 3875083057406769970465767194818051714366) * 10^40
        + 1046594007454693856580563199902554159399) * 10^40
        + 417992587910568601181232896372719981817) * 10^40
        + 627191162563074044093713889668612473962) * 10^40
        + 4350923635082522974021415051787780489216)))

noncomputable def pairedN02701MinusP014Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP014BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP014Center2553‖ ≤ pairedN02701MinusP014Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP014Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP014Input2553]
  have hs : compactExp2547 pairedN02701MinusP014Input2553 16 =
      (pairedN02701MinusP014Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP014Input2553 16).2 : ℝ) =
      pairedN02701MinusP014Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP014Error2553]
  have h := compactExp_error2547 pairedN02701MinusP014Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP014Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP014Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP014DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP014Factor2553 * embedPair2542
          pairedN02701MinusP014Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP014Factor2553 : ℝ) * pairedN02701MinusP014Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP014Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP014Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP014BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP014Factor2553)

def pairedN02701MinusP015Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((912951341665564226630614693 : ℚ) /
        472236648286964521369600000000))

def pairedN02701MinusP015Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP015Factor2553 : RatPair2542 :=
    ((((((((((((((302964974640047908582017875367254
    * 10^40
        + 1732792426828318138307868887908718136781) * 10^40
        + 5983268136623948290548307253226167068028) * 10^40
        + 9342348669767106067975200632227512504158) * 10^40
        + 7114748295436967785139852541768615432568) * 10^40
        + 2351164687556073293457365798347114137948) * 10^40
        + 280620441319425522381348449710205702745) * 10^40
        + 1866748753988487014419151350126041890820) * 10^40
        + 2792882761165193321673294981930804183653) * 10^40
        + 2358435491119604971903564198297873170085) * 10^40
        + 4684589350168123873915172453500178853526) * 10^40
        + 1133439010798154237330384142809912746633) : ℚ) /
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
    (((-((((((((95397553506856617096 * 10^40
        + 5881234752898369279264231513948957819214) * 10^40
        + 2708139678421319267865752062612309392381) * 10^40
        + 1631071259251571080660117210665648442280) * 10^40
        + 6487723219884014114163468831451885743190) * 10^40
        + 5917028419130776598660202982767708337072) * 10^40
        + 2507637067387194095044156992201788237036) * 10^40
        + 6553978174982588919802695893403154579783) * 10^40
        + 1419438461223313435831567198892251823179)) : ℚ) /
        ((((((((966 * 10^40
        + 1854664759073824730069108812637219606340) * 10^40
        + 5597687691702706787457206187151880564181) * 10^40
        + 1195422202881051970022012443698912848523) * 10^40
        + 3875083057406769970465767194818051714366) * 10^40
        + 1046594007454693856580563199902554159399) * 10^40
        + 417992587910568601181232896372719981817) * 10^40
        + 627191162563074044093713889668612473962) * 10^40
        + 4350923635082522974021415051787780489216)))

noncomputable def pairedN02701MinusP015Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP015BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP015Center2553‖ ≤ pairedN02701MinusP015Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP015Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP015Input2553]
  have hs : compactExp2547 pairedN02701MinusP015Input2553 16 =
      (pairedN02701MinusP015Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP015Input2553 16).2 : ℝ) =
      pairedN02701MinusP015Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP015Error2553]
  have h := compactExp_error2547 pairedN02701MinusP015Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP015Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP015Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP015DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP015Factor2553 * embedPair2542
          pairedN02701MinusP015Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP015Factor2553 : ℝ) * pairedN02701MinusP015Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP015Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP015Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP015BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP015Factor2553)

def pairedN02701MinusP016Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((483342473044070207188278171 : ℚ) /
        236118324143482260684800000000))

def pairedN02701MinusP016Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP016Factor2553 : RatPair2542 :=
    ((((((((((((((75741243659954653119735913867741
    * 10^40
        + 2809498447104743747609167981640112237377) * 10^40
        + 2985985433816699403200474388766421834558) * 10^40
        + 6178365892562106457093097513020960280116) * 10^40
        + 6701819833624515249294606314601413962422) * 10^40
        + 6887705445112684797788952886236731650097) * 10^40
        + 6122831279824044295935643155431293024691) * 10^40
        + 9881450999207967975071243724351266105605) * 10^40
        + 8155024659187424618868824245817389218300) * 10^40
        + 1328459769155458100199572199118313848467) * 10^40
        + 6646247204577458538897369421543436119114) * 10^40
        + 9836080203703121415795869252643179127817) : ℚ) /
        (((((((((((3320612103 * 10^40
        + 8437965726684278518867257569520208937968) * 10^40
        + 8157026809371705852980269361190690977034) * 10^40
        + 8972594986166536530339971253439787878785) * 10^40
        + 4776376438675166042293491090575875763872) * 10^40
        + 3873242968946905066942553124663425413615) * 10^40
        + 4979349395229865645718965385511968755979) * 10^40
        + 7082395517742521647768513644345939096317) * 10^40
        + 9934625312027439249967781888852835839661) * 10^40
        + 2035613069932412407306389150490204710051) * 10^40
        + 4363918052734577448718060945366217312904) * 10^40
        + 9001263976903915566254097095874320531456)),
    (((-((((((((4208848756955009007 * 10^40
        + 9113132012047004689635414906349965058845) * 10^40
        + 8709125359614230807666310691352042278025) * 10^40
        + 4395558265900659400590404700720034878617) * 10^40
        + 1824661044049706632476371336333326285967) * 10^40
        + 2862717985371569926652607672219748154074) * 10^40
        + 5863220089471113025455778832217076258652) * 10^40
        + 7233179335683607765898824023671466891698) * 10^40
        + 1121765529431813806846586835732710133159)) : ℚ) /
        ((((((((40 * 10^40
        + 2577277698294742697086212867193217483597) * 10^40
        + 5233236987154279449477383591131328356840) * 10^40
        + 8799809258453377165417583851820788035355) * 10^40
        + 1411461794058615415436073633117418821431) * 10^40
        + 9210274750310612244024190133329273089974) * 10^40
        + 9600749691162940358382551370682196665909) * 10^40
        + 442799631773461418503904745402858853081) * 10^40
        + 7681288484795105123917558960491157520384)))

noncomputable def pairedN02701MinusP016Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP016BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP016Center2553‖ ≤ pairedN02701MinusP016Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP016Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP016Input2553]
  have hs : compactExp2547 pairedN02701MinusP016Input2553 16 =
      (pairedN02701MinusP016Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP016Input2553 16).2 : ℝ) =
      pairedN02701MinusP016Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP016Error2553]
  have h := compactExp_error2547 pairedN02701MinusP016Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP016Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP016Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP016DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP016Factor2553 * embedPair2542
          pairedN02701MinusP016Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP016Factor2553 : ℝ) * pairedN02701MinusP016Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP016Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP016Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP016BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP016Factor2553)

def pairedN02701MinusP017Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1071059113331693339029979313 : ℚ) /
        472236648286964521369600000000))

def pairedN02701MinusP017Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP017Factor2553 : RatPair2542 :=
    ((((((((((((((302964974639335754359683075026459
    * 10^40
        + 195546315468856415005344320936737611290) * 10^40
        + 1705101228027299293785173071716358890787) * 10^40
        + 5953223443051901825989706957830404626213) * 10^40
        + 6960227453501670087748034838309226511215) * 10^40
        + 1047126218673279625679049908291288046771) * 10^40
        + 9732008859802778865339402165587330832882) * 10^40
        + 2192645472115052905310569717061765639463) * 10^40
        + 6943388489349217278182719983142382933043) * 10^40
        + 7473158393846950649726841936387998712420) * 10^40
        + 8980627945664035346456187096058864922933) * 10^40
        + 5615270725543861165634354339611742749713) : ℚ) /
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
    (((-((((((((37306266832955188658 * 10^40
        + 6909413524585223439998263539287852573552) * 10^40
        + 1537845508970067445120957264451849230664) * 10^40
        + 4691104754217545725975490042159713424709) * 10^40
        + 6800115956430586883979202605054477034267) * 10^40
        + 7174433289644477774355243377661371360031) * 10^40
        + 1572785681803481782825011846593370843416) * 10^40
        + 9594248566790379386010704880516704677132) * 10^40
        + 4252831038655717364613569119665919920573)) : ℚ) /
        ((((((((322 * 10^40
        + 618221586357941576689702937545739868780) * 10^40
        + 1865895897234235595819068729050626854727) * 10^40
        + 398474067627017323340670814566304282841) * 10^40
        + 1291694352468923323488589064939350571455) * 10^40
        + 3682198002484897952193521066634184719799) * 10^40
        + 6805997529303522867060410965457573327272) * 10^40
        + 3542397054187691348031237963222870824654) * 10^40
        + 1450307878360840991340471683929260163072)))

noncomputable def pairedN02701MinusP017Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP017BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP017Center2553‖ ≤ pairedN02701MinusP017Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP017Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP017Input2553]
  have hs : compactExp2547 pairedN02701MinusP017Input2553 16 =
      (pairedN02701MinusP017Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP017Input2553 16).2 : ℝ) =
      pairedN02701MinusP017Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP017Error2553]
  have h := compactExp_error2547 pairedN02701MinusP017Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP017Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP017Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP017DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP017Factor2553 * embedPair2542
          pairedN02701MinusP017Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP017Factor2553 : ℝ) * pairedN02701MinusP017Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP017Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP017Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP017BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP017Factor2553)

def pairedN02701MinusP018Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((277630191250842385602313847 : ℚ) /
        118059162071741130342400000000))

def pairedN02701MinusP018Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP018Factor2553 : RatPair2542 :=
    ((((((((((((((18935310914946269371748103709821
    * 10^40
        + 6808282223713644470751737533753641771631) * 10^40
        + 3745842535294766789247099131735993625620) * 10^40
        + 1003681839311956541765871661528307232106) * 10^40
        + 2369389810619364737253491004125122862697) * 10^40
        + 2388779723591687571162513287432034682157) * 10^40
        + 7348303288185448603077292475509549355826) * 10^40
        + 2089011811165878475700273840951982242218) * 10^40
        + 4306826923879729582053825015418493180705) * 10^40
        + 1786994046480970958620706850414067763079) * 10^40
        + 5107673108884009017920773638400979876152) * 10^40
        + 1237038369920744170998821132956947732993) : ℚ) /
        (((((((((((830153025 * 10^40
        + 9609491431671069629716814392380052234492) * 10^40
        + 2039256702342926463245067340297672744258) * 10^40
        + 7243148746541634132584992813359946969696) * 10^40
        + 3694094109668791510573372772643968940968) * 10^40
        + 968310742236726266735638281165856353403) * 10^40
        + 8744837348807466411429741346377992188994) * 10^40
        + 9270598879435630411942128411086484774079) * 10^40
        + 4983656328006859812491945472213208959915) * 10^40
        + 3008903267483103101826597287622551177512) * 10^40
        + 8590979513183644362179515236341554328226) * 10^40
        + 2250315994225978891563524273968580132864)),
    (((-((((((((1813160777046677388 * 10^40
        + 3194941707099396116586707288196708777258) * 10^40
        + 451150480677810580380950561111012095338) * 10^40
        + 1821207437994957647665927846441868003010) * 10^40
        + 1932239072518827493695081026174739577802) * 10^40
        + 8429199335920321285493818393044923602589) * 10^40
        + 986870813006812181577358336788486824412) * 10^40
        + 8214416009532207500353475037046578874735) * 10^40
        + 3284452722038655826981830775891717031121)) : ℚ) /
        ((((((((15 * 10^40
        + 966479136860528511407329825197456556349) * 10^40
        + 712463870182854793554018846674248133815) * 10^40
        + 3299928471920016437031593944432795513258) * 10^40
        + 1779298172771980780788527612419032058036) * 10^40
        + 9703853031366479591509071299998477408740) * 10^40
        + 6100281134186102634393456764005823749715) * 10^40
        + 8916049861915048031938964279526072069905) * 10^40
        + 6630483181798164421469084610184184070144)))

noncomputable def pairedN02701MinusP018Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP018BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP018Center2553‖ ≤ pairedN02701MinusP018Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP018Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP018Input2553]
  have hs : compactExp2547 pairedN02701MinusP018Input2553 16 =
      (pairedN02701MinusP018Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP018Input2553 16).2 : ℝ) =
      pairedN02701MinusP018Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP018Error2553]
  have h := compactExp_error2547 pairedN02701MinusP018Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP018Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP018Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP018DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP018Factor2553 * embedPair2542
          pairedN02701MinusP018Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP018Factor2553 : ℝ) * pairedN02701MinusP018Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP018Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP018Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP018BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP018Factor2553)

def pairedN02701MinusP019Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((59091935462568230097122829 : ℚ) /
        23611832414348226068480000000))

def pairedN02701MinusP019Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP019Factor2553 : RatPair2542 :=
    ((((((((((((((18935310914923072018560276063679
    * 10^40
        + 1988279420953882353844875286025144648127) * 10^40
        + 2603983159771986243375990271989986272487) * 10^40
        + 4340210256593432340604054238143012794816) * 10^40
        + 719977348121248596730939371530033169182) * 10^40
        + 185826292347572552252648895057053331667) * 10^40
        + 2326003754391955884334260451796027564065) * 10^40
        + 8149234851907645849790883255506035264060) * 10^40
        + 964170807709548519046362857847950655737) * 10^40
        + 9277767720567301003466000946599611460556) * 10^40
        + 7383372492580490468436930671861740795541) * 10^40
        + 7042740300322806501329662209192801389617) : ℚ) /
        (((((((((((830153025 * 10^40
        + 9609491431671069629716814392380052234492) * 10^40
        + 2039256702342926463245067340297672744258) * 10^40
        + 7243148746541634132584992813359946969696) * 10^40
        + 3694094109668791510573372772643968940968) * 10^40
        + 968310742236726266735638281165856353403) * 10^40
        + 8744837348807466411429741346377992188994) * 10^40
        + 9270598879435630411942128411086484774079) * 10^40
        + 4983656328006859812491945472213208959915) * 10^40
        + 3008903267483103101826597287622551177512) * 10^40
        + 8590979513183644362179515236341554328226) * 10^40
        + 2250315994225978891563524273968580132864)),
    (((-((((((((643200817712235797 * 10^40
        + 328299285808509969953132070779985374546) * 10^40
        + 2525435610886176998073668489039297943232) * 10^40
        + 523979433574149819811569406187796532185) * 10^40
        + 6952583823154863008488901460211596864268) * 10^40
        + 1865581720974866232896589075700551509447) * 10^40
        + 5322856196876375905847351142520880742566) * 10^40
        + 9589949151179391457211261914500087988323) * 10^40
        + 3219383308981277111343558499779906753965)) : ℚ) /
        ((((((((5 * 10^40
        + 322159712286842837135776608399152185449) * 10^40
        + 6904154623394284931184672948891416044605) * 10^40
        + 1099976157306672145677197981477598504419) * 10^40
        + 3926432724257326926929509204139677352678) * 10^40
        + 9901284343788826530503023766666159136246) * 10^40
        + 8700093711395367544797818921335274583238) * 10^40
        + 6305349953971682677312988093175357356635) * 10^40
        + 2210161060599388140489694870061394690048)))

noncomputable def pairedN02701MinusP019Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP019BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP019Center2553‖ ≤ pairedN02701MinusP019Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP019Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP019Input2553]
  have hs : compactExp2547 pairedN02701MinusP019Input2553 16 =
      (pairedN02701MinusP019Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP019Input2553 16).2 : ℝ) =
      pairedN02701MinusP019Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP019Error2553]
  have h := compactExp_error2547 pairedN02701MinusP019Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP019Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP019Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP019DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP019Factor2553 * embedPair2542
          pairedN02701MinusP019Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP019Factor2553 : ℝ) * pairedN02701MinusP019Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP019Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP019Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP019BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP019Factor2553)

def pairedN02701MinusP020Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1259391271552815101014882561 : ℚ) /
        472236648286964521369600000000))

def pairedN02701MinusP020Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP020Factor2553 : RatPair2542 :=
    ((((((((((((((302964974638339337140877859774166
    * 10^40
        + 4440281384202488479170990578940139410092) * 10^40
        + 3358274408266155570179596635723791646477) * 10^40
        + 803869825541842939350370849907091459580) * 10^40
        + 1273814967443757961950534409757394445883) * 10^40
        + 5738699171880388892577831340479925912355) * 10^40
        + 1994508054453782552092156111251871378877) * 10^40
        + 6610598910242937526477281116104483996881) * 10^40
        + 5666186851434484068405178517168606137313) * 10^40
        + 993939085184682709019844523205452855678) * 10^40
        + 4889044437673779057381275755649164750838) * 10^40
        + 9269159894308475616692658099678513912241) : ℚ) /
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
    (((-((((((((131598301827090994819 * 10^40
        + 5911106341538819119237895774185990201853) * 10^40
        + 8319723029036120791492401487462212260769) * 10^40
        + 3591784109381288516015742660422618639304) * 10^40
        + 7525433045033277585651780310159049975358) * 10^40
        + 4061101666483939054850146939188758346417) * 10^40
        + 5502505760548119391592218135404547671126) * 10^40
        + 7257546023432340788284289897762175242542) * 10^40
        + 5491676402965088137368978356055640302279)) : ℚ) /
        ((((((((966 * 10^40
        + 1854664759073824730069108812637219606340) * 10^40
        + 5597687691702706787457206187151880564181) * 10^40
        + 1195422202881051970022012443698912848523) * 10^40
        + 3875083057406769970465767194818051714366) * 10^40
        + 1046594007454693856580563199902554159399) * 10^40
        + 417992587910568601181232896372719981817) * 10^40
        + 627191162563074044093713889668612473962) * 10^40
        + 4350923635082522974021415051787780489216)))

noncomputable def pairedN02701MinusP020Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP020BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP020Center2553‖ ≤ pairedN02701MinusP020Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP020Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP020Input2553]
  have hs : compactExp2547 pairedN02701MinusP020Input2553 16 =
      (pairedN02701MinusP020Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP020Input2553 16).2 : ℝ) =
      pairedN02701MinusP020Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP020Error2553]
  have h := compactExp_error2547 pairedN02701MinusP020Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP020Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP020Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP020DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP020Factor2553 * embedPair2542
          pairedN02701MinusP020Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP020Factor2553 : ℝ) * pairedN02701MinusP020Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP020Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP020Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP020BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP020Factor2553)

def pairedN02701MinusP021Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1324111916357314294844085153 : ℚ) /
        472236648286964521369600000000))

def pairedN02701MinusP021Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP021Factor2553 : RatPair2542 :=
    ((((((((((((((302964974637959734944564754669386
    * 10^40
        + 3444108035321634714209757628505216871295) * 10^40
        + 5214821531040899095026419332990734327392) * 10^40
        + 7877811732069189019895031532170409675899) * 10^40
        + 4403675515071461965194000443205092736779) * 10^40
        + 6280512723960508281976839868742979759261) * 10^40
        + 5126252470174858348568600333696232165291) * 10^40
        + 3058739665291471888586821258896533017534) * 10^40
        + 2144477554394499001429199266240777747424) * 10^40
        + 3548124409106882275098518887872170900096) * 10^40
        + 7560609384365817484602041262679311483835) * 10^40
        + 9987014252440505988107567224341836549873) : ℚ) /
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
    (((-((((((((46120397887879092906 * 10^40
        + 3852422331108642673673431372407961983758) * 10^40
        + 8042092745578776167910601722577740211921) * 10^40
        + 1418918017663769226501867563996993214327) * 10^40
        + 912590059989304520200063631456176684598) * 10^40
        + 3923516928426451059086691060180416391086) * 10^40
        + 541114055768816979183825814594132473402) * 10^40
        + 1214729618310901759804200665210825945413) * 10^40
        + 4680021718520032492921977654057556569933)) : ℚ) /
        ((((((((322 * 10^40
        + 618221586357941576689702937545739868780) * 10^40
        + 1865895897234235595819068729050626854727) * 10^40
        + 398474067627017323340670814566304282841) * 10^40
        + 1291694352468923323488589064939350571455) * 10^40
        + 3682198002484897952193521066634184719799) * 10^40
        + 6805997529303522867060410965457573327272) * 10^40
        + 3542397054187691348031237963222870824654) * 10^40
        + 1450307878360840991340471683929260163072)))

noncomputable def pairedN02701MinusP021Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP021BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP021Center2553‖ ≤ pairedN02701MinusP021Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP021Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP021Input2553]
  have hs : compactExp2547 pairedN02701MinusP021Input2553 16 =
      (pairedN02701MinusP021Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP021Input2553 16).2 : ℝ) =
      pairedN02701MinusP021Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP021Error2553]
  have h := compactExp_error2547 pairedN02701MinusP021Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP021Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP021Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP021DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP021Factor2553 * embedPair2542
          pairedN02701MinusP021Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP021Factor2553 : ℝ) * pairedN02701MinusP021Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP021Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP021Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP021BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP021Factor2553)

def pairedN02701MinusP022Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((271447665815041436069447627 : ℚ) /
        94447329657392904273920000000))

def pairedN02701MinusP022Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP022Factor2553 : RatPair2542 :=
    ((((((((((((((302964974637758081876450152309583
    * 10^40
        + 4393356384770663540056380515143064418467) * 10^40
        + 2510809093974262344329423319469907288415) * 10^40
        + 2636425558499308226010058922466487592446) * 10^40
        + 9663107157648117472699680856677137008213) * 10^40
        + 5931238961917124576256876440355725176033) * 10^40
        + 1641861632114132199730804186017678010038) * 10^40
        + 7517520435588980910323539493691194097393) * 10^40
        + 9628278205160897879650789216248323856081) * 10^40
        + 7990198249299597711745761388770127455200) * 10^40
        + 5583285584756093274248645413937012475382) * 10^40
        + 3347760550099410438632446136039316951297) : ℚ) /
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
    (((-((((((((141822691101132755097 * 10^40
        + 8372648655754688525194089208969069992301) * 10^40
        + 8312310425949097499066072272271313492337) * 10^40
        + 3367086119035547272992724964127325341842) * 10^40
        + 2738518645661742224406854382207106245139) * 10^40
        + 7961910022564112061276824567107752174230) * 10^40
        + 4821539492326387874690099514527869399491) * 10^40
        + 5012066567518817031952543908858453203152) * 10^40
        + 6548771772509038596204233347416040488785)) : ℚ) /
        ((((((((966 * 10^40
        + 1854664759073824730069108812637219606340) * 10^40
        + 5597687691702706787457206187151880564181) * 10^40
        + 1195422202881051970022012443698912848523) * 10^40
        + 3875083057406769970465767194818051714366) * 10^40
        + 1046594007454693856580563199902554159399) * 10^40
        + 417992587910568601181232896372719981817) * 10^40
        + 627191162563074044093713889668612473962) * 10^40
        + 4350923635082522974021415051787780489216)))

noncomputable def pairedN02701MinusP022Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP022BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP022Center2553‖ ≤ pairedN02701MinusP022Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP022Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP022Input2553]
  have hs : compactExp2547 pairedN02701MinusP022Input2553 16 =
      (pairedN02701MinusP022Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP022Input2553 16).2 : ℝ) =
      pairedN02701MinusP022Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP022Error2553]
  have h := compactExp_error2547 pairedN02701MinusP022Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP022Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP022Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP022DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP022Factor2553 * embedPair2542
          pairedN02701MinusP022Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP022Factor2553 : ℝ) * pairedN02701MinusP022Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP022Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP022Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP022BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP022Factor2553)

def pairedN02701MinusP023Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((726373966280652557447321527 : ℚ) /
        236118324143482260684800000000))

def pairedN02701MinusP023Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP023Factor2553 : RatPair2542 :=
    ((((((((((((((75741243659287196542440117617712
    * 10^40
        + 8738840180402406171538158638247390209491) * 10^40
        + 9125157590281365430809441798415714804157) * 10^40
        + 7472005140330575687828348347495894982333) * 10^40
        + 3799027492124651763947499355372849060145) * 10^40
        + 9764999298763242701527508695107896998279) * 10^40
        + 9770003938954434470923951679725603848286) * 10^40
        + 7793283860173434456370566898271494026361) * 10^40
        + 2587395418361446969936959149195403452540) * 10^40
        + 339813746092685067782336800489257268430) * 10^40
        + 8686837204622532114123156924944983277510) * 10^40
        + 8899178692813931455345913328688784075649) : ℚ) /
        (((((((((((3320612103 * 10^40
        + 8437965726684278518867257569520208937968) * 10^40
        + 8157026809371705852980269361190690977034) * 10^40
        + 8972594986166536530339971253439787878785) * 10^40
        + 4776376438675166042293491090575875763872) * 10^40
        + 3873242968946905066942553124663425413615) * 10^40
        + 4979349395229865645718965385511968755979) * 10^40
        + 7082395517742521647768513644345939096317) * 10^40
        + 9934625312027439249967781888852835839661) * 10^40
        + 2035613069932412407306389150490204710051) * 10^40
        + 4363918052734577448718060945366217312904) * 10^40
        + 9001263976903915566254097095874320531456)),
    (((-((((((((18975353929529766981 * 10^40
        + 7135947909192414080621753680438519530731) * 10^40
        + 2625682259009124549046998676017054736112) * 10^40
        + 5278168207854242373167956864235516070903) * 10^40
        + 4013420243568635114719938829129572971167) * 10^40
        + 4181791484836619705556507179670287977518) * 10^40
        + 6722398607759294842632916523296077889199) * 10^40
        + 6400052141016485316236133685324518133448) * 10^40
        + 7674382063209468507662794063426400357137)) : ℚ) /
        ((((((((120 * 10^40
        + 7731833094884228091258638601579652450792) * 10^40
        + 5699710961462838348432150773393985070522) * 10^40
        + 6399427775360131496252751555462364106065) * 10^40
        + 4234385382175846246308220899352256464295) * 10^40
        + 7630824250931836732072570399987819269924) * 10^40
        + 8802249073488821075147654112046589997727) * 10^40
        + 1328398895320384255511714236208576559245) * 10^40
        + 3043865454385315371752676881473472561152)))

noncomputable def pairedN02701MinusP023Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP023BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP023Center2553‖ ≤ pairedN02701MinusP023Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP023Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP023Input2553]
  have hs : compactExp2547 pairedN02701MinusP023Input2553 16 =
      (pairedN02701MinusP023Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP023Input2553 16).2 : ℝ) =
      pairedN02701MinusP023Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP023Error2553]
  have h := compactExp_error2547 pairedN02701MinusP023Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP023Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP023Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP023DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP023Factor2553 * embedPair2542
          pairedN02701MinusP023Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP023Factor2553 : ℝ) * pairedN02701MinusP023Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP023Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP023Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP023BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP023Factor2553)

def pairedN02701MinusP024Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((748320139291177557999687593 : ℚ) /
        236118324143482260684800000000))

def pairedN02701MinusP024Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP024Factor2553 : RatPair2542 :=
    ((((((((((((((75741243659213721876153408348942
    * 10^40
        + 130878978763448644037085279902293298153) * 10^40
        + 5637299989509367677091051697781806893288) * 10^40
        + 8721101312658152963947667814675374713268) * 10^40
        + 4952911862096984297370669737826738034427) * 10^40
        + 8084212237454865223095175740482640509157) * 10^40
        + 5276746841018960634174902566307551975273) * 10^40
        + 4475362529265148111594226953961709153948) * 10^40
        + 1351176195177832322572383744663878154897) * 10^40
        + 9905577676775875276774140168947945273375) * 10^40
        + 3072044836254372623727031356386542138517) * 10^40
        + 2509918303612625927461280664639299262529) : ℚ) /
        (((((((((((3320612103 * 10^40
        + 8437965726684278518867257569520208937968) * 10^40
        + 8157026809371705852980269361190690977034) * 10^40
        + 8972594986166536530339971253439787878785) * 10^40
        + 4776376438675166042293491090575875763872) * 10^40
        + 3873242968946905066942553124663425413615) * 10^40
        + 4979349395229865645718965385511968755979) * 10^40
        + 7082395517742521647768513644345939096317) * 10^40
        + 9934625312027439249967781888852835839661) * 10^40
        + 2035613069932412407306389150490204710051) * 10^40
        + 4363918052734577448718060945366217312904) * 10^40
        + 9001263976903915566254097095874320531456)),
    (((-((((((((19548662472516527635 * 10^40
        + 7746935627995071299154939632624331662433) * 10^40
        + 309303540448472929621214921634394757317) * 10^40
        + 3810390151292591314893618569770601249340) * 10^40
        + 8900315713762011226556255564012902674718) * 10^40
        + 2888064500183914792085779761654301193298) * 10^40
        + 1115706458178398457566221702083666004825) * 10^40
        + 1719429221489488820164289021534095257614) * 10^40
        + 1358996506978115674759879782769639782863)) : ℚ) /
        ((((((((120 * 10^40
        + 7731833094884228091258638601579652450792) * 10^40
        + 5699710961462838348432150773393985070522) * 10^40
        + 6399427775360131496252751555462364106065) * 10^40
        + 4234385382175846246308220899352256464295) * 10^40
        + 7630824250931836732072570399987819269924) * 10^40
        + 8802249073488821075147654112046589997727) * 10^40
        + 1328398895320384255511714236208576559245) * 10^40
        + 3043865454385315371752676881473472561152)))

noncomputable def pairedN02701MinusP024Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP024BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP024Center2553‖ ≤ pairedN02701MinusP024Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP024Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP024Input2553]
  have hs : compactExp2547 pairedN02701MinusP024Input2553 16 =
      (pairedN02701MinusP024Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP024Input2553 16).2 : ℝ) =
      pairedN02701MinusP024Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP024Error2553]
  have h := compactExp_error2547 pairedN02701MinusP024Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP024Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP024Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP024DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP024Factor2553 * embedPair2542
          pairedN02701MinusP024Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP024Factor2553 : ℝ) * pairedN02701MinusP024Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP024Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP024Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP024BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP024Factor2553)

def pairedN02701MinusP025Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((24244894162688885003625027 : ℚ) /
        7378697629483820646400000000))

def pairedN02701MinusP025Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP025Factor2553 : RatPair2542 := ((((((((((((((73966058260857918172398093051 *
    10^40
        + 6959814662640733832367709354938054520787) * 10^40
        + 8493559378773213411671835538257127372889) * 10^40
        + 1109450924347830793103119449179554771410) * 10^40
        + 8160462140044624748451361213334833939513) * 10^40
        + 7952625153951556040232172222895258365144) * 10^40
        + 2348089249816575793441981808445934352602) * 10^40
        + 1523903381054691649524673571787364573918) * 10^40
        + 7704143180660397530505463125244427044992) * 10^40
        + 9699857667677105204427139013503940104911) * 10^40
        + 7649910576572899853290761400298020345932) * 10^40
        + 1024647795267801089575510665200330992313) : ℚ) /
        (((((((((((3242785 * 10^40
        + 2576599575904965115741081306220234579040) * 10^40
        + 9851715846493527056497051044298037784157) * 10^40
        + 2606418549791178258330410128177187292850) * 10^40
        + 3764430055115893716838177237393140503675) * 10^40
        + 6566282463836862211979436087035804126380) * 10^40
        + 4838847020893779165669647427134289031988) * 10^40
        + 2614338276872795431296648939105806581148) * 10^40
        + 7480404907531276796142546662000832847499) * 10^40
        + 6691441028388605871491510145654775590537) * 10^40
        + 1596058513723373610789763731391959196594) * 10^40
        + 6336915296852445230045170016695189766144)),
    (((-((((((((206171531020680 * 10^40
        + 7715204052236023510986564581175588078272) * 10^40
        + 9570552133509681884234346267606220367571) * 10^40
        + 5258137714065884722084983473275699627391) * 10^40
        + 350085470489898445656750589790862866135) * 10^40
        + 9974738389740596614745091851803446246660) * 10^40
        + 1673577165356470507697485603574390644722) * 10^40
        + 5240727880667604117948099479213759293523) * 10^40
        + 214279528204932718097240576700644905407)) : ℚ) /
        (((((((12285683523507529989535101711034949264 * 10^40
        + 258033240874852120344527508044162943370) * 10^40
        + 2649194330116529949254315722163446679322) * 10^40
        + 3680157820489320636456769899708041913416) * 10^40
        + 1813940743247995318977173589786783730257) * 10^40
        + 8727709983816258634654491655010091619771) * 10^40
        + 2984937829578606367841140866233685389979) * 10^40
        + 6472707558852685397495236741911636082688)))

noncomputable def pairedN02701MinusP025Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP025BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP025Center2553‖ ≤ pairedN02701MinusP025Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP025Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP025Input2553]
  have hs : compactExp2547 pairedN02701MinusP025Input2553 16 =
      (pairedN02701MinusP025Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP025Input2553 16).2 : ℝ) =
      pairedN02701MinusP025Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP025Error2553]
  have h := compactExp_error2547 pairedN02701MinusP025Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP025Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP025Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP025DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP025Factor2553 * embedPair2542
          pairedN02701MinusP025Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP025Factor2553 : ℝ) * pairedN02701MinusP025Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP025Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP025Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP025BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP025Factor2553)

def pairedN02701MinusP026Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((50247333217324293119390103 : ℚ) /
        14757395258967641292800000000))

def pairedN02701MinusP026Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP026Factor2553 : RatPair2542 := ((((((((((((((295864233043037702130982678421
    *
    10^40
        + 3108882113524601892885677746696328983952) * 10^40
        + 3360964155587875803192688689473476245725) * 10^40
        + 9390777130147003185669921305414679455071) * 10^40
        + 2535562836940197568782251271972174802446) * 10^40
        + 5211278651179616010583383622731798107498) * 10^40
        + 1336059759756603293403713618413520246250) * 10^40
        + 9506259379125269276340220162762693329644) * 10^40
        + 1879954960076891298026157872974492960364) * 10^40
        + 1811773003055667832365397297430138138369) * 10^40
        + 7354696007480029169424585226286284738611) * 10^40
        + 8530341926294383935298309879770156923329) : ℚ) /
        (((((((((((12971141 * 10^40
        + 306398303619860462964325224880938316163) * 10^40
        + 9406863385974108225988204177192151136629) * 10^40
        + 425674199164713033321640512708749171401) * 10^40
        + 5057720220463574867352708949572562014702) * 10^40
        + 6265129855347448847917744348143216505521) * 10^40
        + 9355388083575116662678589708537156127953) * 10^40
        + 457353107491181725186595756423226324594) * 10^40
        + 9921619630125107184570186648003331389998) * 10^40
        + 6765764113554423485966040582619102362148) * 10^40
        + 6384234054893494443159054925567836786378) * 10^40
        + 5347661187409780920180680066780759064576)),
    (((-((((((((1709154851261531 * 10^40
        + 9354105643940709168452484861755112717128) * 10^40
        + 7746496863754747650742393463381893385181) * 10^40
        + 662701183289186743669390960044509483890) * 10^40
        + 230871886680132051779623489796690950421) * 10^40
        + 5482667713258543385252324479352628044132) * 10^40
        + 4243413679141306380467386835895288059671) * 10^40
        + 9195892682893260288868897047358302708023) * 10^40
        + 977680104979312607004290525597901494651)) : ℚ) /
        (((((((98285468188060239916280813688279594112 * 10^40
        + 2064265926998816962756220064353303546962) * 10^40
        + 1193554640932239594034525777307573434578) * 10^40
        + 9441262563914565091654159197664335307329) * 10^40
        + 4511525945983962551817388718294269842062) * 10^40
        + 9821679870530069077235933240080732958170) * 10^40
        + 3879502636628850942729126929869483119837) * 10^40
        + 1781660470821483179961893935293088661504)))

noncomputable def pairedN02701MinusP026Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP026BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP026Center2553‖ ≤ pairedN02701MinusP026Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP026Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP026Input2553]
  have hs : compactExp2547 pairedN02701MinusP026Input2553 16 =
      (pairedN02701MinusP026Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP026Input2553 16).2 : ℝ) =
      pairedN02701MinusP026Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP026Error2553]
  have h := compactExp_error2547 pairedN02701MinusP026Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP026Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP026Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP026DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP026Factor2553 * embedPair2542
          pairedN02701MinusP026Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP026Factor2553 : ℝ) * pairedN02701MinusP026Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP026Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP026Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP026BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP026Factor2553)

def pairedN02701MinusP027Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((105567055574838531593598713 : ℚ) /
        29514790517935282585600000000))

def pairedN02701MinusP027Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP027Factor2553 : RatPair2542 := ((((((((((((((1183456932169777868463976759072
    *
    10^40
        + 4136112744558443807926136742737270751759) * 10^40
        + 4626689050463007445900123804737067556146) * 10^40
        + 5863366311396412854516064814692770045370) * 10^40
        + 4879911861356217322168574901689391347630) * 10^40
        + 251863701594703940126178138148322874489) * 10^40
        + 151094398845737756150979033032516888785) * 10^40
        + 6770484880995692524400559475468136166473) * 10^40
        + 152780099376210839673761450819281128015) * 10^40
        + 321590393608904362931202909847174894594) * 10^40
        + 6033331339910348039395622919805186748578) * 10^40
        + 3496729933213727379954362804341691094753) : ℚ) /
        (((((((((((51884564 * 10^40
        + 1225593214479441851857300899523753264655) * 10^40
        + 7627453543896432903952816708768604546516) * 10^40
        + 1702696796658852133286562050834996685606) * 10^40
        + 230880881854299469410835798290248058810) * 10^40
        + 5060519421389795391670977392572866022087) * 10^40
        + 7421552334300466650714358834148624511812) * 10^40
        + 1829412429964726900746383025692905298379) * 10^40
        + 9686478520500428738280746592013325559994) * 10^40
        + 7063056454217693943864162330476409448594) * 10^40
        + 5536936219573977772636219702271347145514) * 10^40
        + 1390644749639123680722720267123036258304)),
    (((-((((((((43090154310569133 * 10^40
        + 4590834779372845248089669319816040616609) * 10^40
        + 305060558600553552035727380449819750767) * 10^40
        + 6955245623331464880806617703034599256022) * 10^40
        + 8059880241689772948257052169984041218753) * 10^40
        + 2682866111341306649002120619312270729007) * 10^40
        + 1808507114066266162482340317239793179753) * 10^40
        + 6672717795996057673543707186726586678785) * 10^40
        + 1606804177219682698375041161104754787679)) : ℚ) /
        (((((((2358851236513445757990739528518710258692 * 10^40
        + 9542382247971607106149281544479285127090) * 10^40
        + 8645311382373750256828618655381762429894) * 10^40
        + 6590301533949562199699820743944047375906) * 10^40
        + 8276622703615101243617329239062476209511) * 10^40
        + 5720316892721657853662397761937590996089) * 10^40
        + 3108063279092422625499046316867594876092) * 10^40
        + 2759851299715596319085454447034127876096)))

noncomputable def pairedN02701MinusP027Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP027BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP027Center2553‖ ≤ pairedN02701MinusP027Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP027Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP027Input2553]
  have hs : compactExp2547 pairedN02701MinusP027Input2553 16 =
      (pairedN02701MinusP027Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP027Input2553 16).2 : ℝ) =
      pairedN02701MinusP027Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP027Error2553]
  have h := compactExp_error2547 pairedN02701MinusP027Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP027Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP027Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP027DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP027Factor2553 * embedPair2542
          pairedN02701MinusP027Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP027Factor2553 : ℝ) * pairedN02701MinusP027Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP027Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP027Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP027BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP027Factor2553)

def pairedN02701MinusP028Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((430301136886435135522330613 : ℚ) /
        118059162071741130342400000000))

def pairedN02701MinusP028Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP028Factor2553 : RatPair2542 :=
    ((((((((((((((18935310914700897708656756641189
    * 10^40
        + 6939270781282501025140597439584288282331) * 10^40
        + 3521985997725835780474612562488332697222) * 10^40
        + 8069525232557547672856240406686130998998) * 10^40
        + 5377613680528039118170913645000735863595) * 10^40
        + 3721801257663710801941177781533379150594) * 10^40
        + 9851397803458659409535292309358266834311) * 10^40
        + 7836204115528618798508543428071543019379) * 10^40
        + 500309841464037921663314696895175803162) * 10^40
        + 2881883925064734258951678367476901323431) * 10^40
        + 1605508818351397950885371090474806820153) * 10^40
        + 3645096151742168133079063474268267877033) : ℚ) /
        (((((((((((830153025 * 10^40
        + 9609491431671069629716814392380052234492) * 10^40
        + 2039256702342926463245067340297672744258) * 10^40
        + 7243148746541634132584992813359946969696) * 10^40
        + 3694094109668791510573372772643968940968) * 10^40
        + 968310742236726266735638281165856353403) * 10^40
        + 8744837348807466411429741346377992188994) * 10^40
        + 9270598879435630411942128411086484774079) * 10^40
        + 4983656328006859812491945472213208959915) * 10^40
        + 3008903267483103101826597287622551177512) * 10^40
        + 8590979513183644362179515236341554328226) * 10^40
        + 2250315994225978891563524273968580132864)),
    (((-((((((((255475602342158616 * 10^40
        + 5811271786762149102120169241642879037908) * 10^40
        + 6448611421914921553614728827759609863505) * 10^40
        + 5763820638517133873225469214509909267139) * 10^40
        + 5535708311844732588197064462964029261778) * 10^40
        + 3854930843196945395798444298538870578146) * 10^40
        + 1374024788608520721071794405205314121641) * 10^40
        + 6808048128762396646609462417408403379260) * 10^40
        + 6843730582180260836775676363645023239409)) : ℚ) /
        ((((((((1 * 10^40
        + 3724225376078229864673393620472496050577) * 10^40
        + 1882951260925714072141274440606749830346) * 10^40
        + 8481811679265456039730144904039345046659) * 10^40
        + 8343572561161089161889866146583548368912) * 10^40
        + 4518532093760589053773551936363497946249) * 10^40
        + 1463661921289645694035768796727802159065) * 10^40
        + 810549987446822548358087661775097460900) * 10^40
        + 5148225743799833129224462237289471279104)))

noncomputable def pairedN02701MinusP028Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP028BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP028Center2553‖ ≤ pairedN02701MinusP028Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP028Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP028Input2553]
  have hs : compactExp2547 pairedN02701MinusP028Input2553 16 =
      (pairedN02701MinusP028Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP028Input2553 16).2 : ℝ) =
      pairedN02701MinusP028Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP028Error2553]
  have h := compactExp_error2547 pairedN02701MinusP028Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP028Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP028Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP028DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP028Factor2553 * embedPair2542
          pairedN02701MinusP028Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP028Factor2553 : ℝ) * pairedN02701MinusP028Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP028Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP028Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP028BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP028Factor2553)

def pairedN02701MinusP029Input2553 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((442530733595656525480647121 : ℚ) /
        118059162071741130342400000000))

def pairedN02701MinusP029Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701MinusP029Factor2553 : RatPair2542 :=
    ((((((((((((((18935310914676664015164049648393
    * 10^40
        + 5328246568460983480727876035447758380436) * 10^40
        + 3105800728868644912439957033061766640175) * 10^40
        + 8028131411231622379154706455844498061745) * 10^40
        + 5358354040821189818687378819529064671289) * 10^40
        + 4928284655958393012855616496804818611586) * 10^40
        + 659081615469600959220813431223942039583) * 10^40
        + 5091197163592277440890339616368440290358) * 10^40
        + 3516439559082143334039328887348330242459) * 10^40
        + 9963126712569338558420587980464603951345) * 10^40
        + 8141512347582973089446835701936003776180) * 10^40
        + 4678723578283942551103847302227275420241) : ℚ) /
        (((((((((((830153025 * 10^40
        + 9609491431671069629716814392380052234492) * 10^40
        + 2039256702342926463245067340297672744258) * 10^40
        + 7243148746541634132584992813359946969696) * 10^40
        + 3694094109668791510573372772643968940968) * 10^40
        + 968310742236726266735638281165856353403) * 10^40
        + 8744837348807466411429741346377992188994) * 10^40
        + 9270598879435630411942128411086484774079) * 10^40
        + 4983656328006859812491945472213208959915) * 10^40
        + 3008903267483103101826597287622551177512) * 10^40
        + 8590979513183644362179515236341554328226) * 10^40
        + 2250315994225978891563524273968580132864)),
    (((-((((((((2890101271684489191 * 10^40
        + 56210078142341889558041035666511908460) * 10^40
        + 5192617881503843916901506235243836818494) * 10^40
        + 4229013685239231931012116915138787091144) * 10^40
        + 4385294784958355551037277288215039437294) * 10^40
        + 6000738520975163185669970812924364171110) * 10^40
        + 2910960965779102002417447581410394885119) * 10^40
        + 1610054218821235389554645726927029463697) * 10^40
        + 2573109238100138283821068006687062426839)) : ℚ) /
        ((((((((15 * 10^40
        + 966479136860528511407329825197456556349) * 10^40
        + 712463870182854793554018846674248133815) * 10^40
        + 3299928471920016437031593944432795513258) * 10^40
        + 1779298172771980780788527612419032058036) * 10^40
        + 9703853031366479591509071299998477408740) * 10^40
        + 6100281134186102634393456764005823749715) * 10^40
        + 8916049861915048031938964279526072069905) * 10^40
        + 6630483181798164421469084610184184070144)))

noncomputable def pairedN02701MinusP029Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701MinusP029BaseError2553 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP029Center2553‖ ≤ pairedN02701MinusP029Error2553 := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701MinusP029Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701MinusP029Input2553]
  have hs : compactExp2547 pairedN02701MinusP029Input2553 16 =
      (pairedN02701MinusP029Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701MinusP029Input2553 16).2 : ℝ) =
      pairedN02701MinusP029Error2553 := by
    rw [hs]
    norm_num [pairedN02701MinusP029Error2553]
  have h := compactExp_error2547 pairedN02701MinusP029Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      pairedN02701MinusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701MinusP029Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701MinusPosition2553, storedWidth,
        nodeModulation2541,
      embedPair2542, pairedN02701MinusP029Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701MinusP029DerivativeError2553 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN02701MinusPosition2553
        -
      embedPair2542 pairedN02701MinusP029Factor2553 * embedPair2542
          pairedN02701MinusP029Center2553‖ ≤
        (pairMagnitude2542 pairedN02701MinusP029Factor2553 : ℝ) * pairedN02701MinusP029Error2553
            := by
  have hx : |pairedN02701MinusPosition2553| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [pairedN02701MinusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) pairedN02701MinusPosition2553 = embedPair2542
          pairedN02701MinusP029Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701MinusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701MinusP029Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701MinusP029BaseError2553
    (embedPair_magnitude2542 pairedN02701MinusP029Factor2553)

theorem pairedN02701MinusGrid2553 :
    -stripRadius2303 + (2701 : ℝ) * (2 * stripRadius2303 / 10240) =
      pairedN02701MinusPosition2553 := by
  norm_num [stripRadius2303, pairedN02701MinusPosition2553]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.pairedN02701MinusP000DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP001DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP002DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP003DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP004DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP005DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP006DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP007DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP008DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP009DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP010DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP011DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP012DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP013DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP014DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP015DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP016DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP017DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP018DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP019DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP020DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP021DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP022DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP023DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP024DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP025DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP026DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP027DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP028DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusP029DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701MinusGrid2553
