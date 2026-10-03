import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def pairedN02701PlusPosition2553 : ℝ := (((-158531586419) : ℝ) /
        51200000000)

theorem pairedN02701PlusZero2553 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def pairedN02701PlusP000Center2553 : RatPair2542 := (0, 0)

def pairedN02701PlusP000Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02701PlusP000Error2553 : ℝ := 0

theorem pairedN02701PlusP000Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN02701PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |pairedN02701PlusPosition2553| := by
    norm_num [storedWidth, pairedN02701PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem pairedN02701PlusP000BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP000Center2553‖ ≤ pairedN02701PlusP000Error2553 := by
  rw [pairedN02701PlusP000Exterior2553]
  norm_num [pairedN02701PlusP000Center2553, pairedN02701PlusP000Error2553,
      pairedN02701PlusZero2553]

theorem pairedN02701PlusP000DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP000Factor2553 * embedPair2542 pairedN02701PlusP000Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP000Factor2553 : ℝ) * pairedN02701PlusP000Error2553 :=
            by
  rw [pairedN02701PlusP000Exterior2553]
  norm_num [pairedN02701PlusP000Factor2553, pairedN02701PlusP000Center2553,
      pairedN02701PlusP000Error2553, pairedN02701PlusZero2553, pairMagnitude2542]

def pairedN02701PlusP001Input2553 : RatPair2542 := ((((-((340 * 10^40
        + 1125558694715412604882605546165965236561) * 10^40
        + 9325600687173468560131001925406640200979)) : ℚ) /
        ((941 * 10^40
        + 6102169216506454849034257242358098754684) * 10^40
        + 4000368461807982441421667880140800000000)),
    ((875774620147323865939848151 : ℚ) /
        3689348814741910323200000000))

def pairedN02701PlusP001Center2553 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP001Factor2553 : RatPair2542 := ((((((((((((((2822667428909 * 10^40
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

noncomputable def pairedN02701PlusP001Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP001BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP001Center2553‖ ≤ pairedN02701PlusP001Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP001Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP001Input2553]
  have hs : compactExp2547 pairedN02701PlusP001Input2553 9 =
      (pairedN02701PlusP001Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP001Input2553 9).2 : ℝ) =
      pairedN02701PlusP001Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP001Error2553]
  have h := compactExp_error2547 pairedN02701PlusP001Input2553 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          pairedN02701PlusP001Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP001Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP001DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP001Factor2553 * embedPair2542 pairedN02701PlusP001Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP001Factor2553 : ℝ) * pairedN02701PlusP001Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP001Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP001Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP001BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP001Factor2553)

def pairedN02701PlusP002Input2553 : RatPair2542 := ((((-((9033 * 10^40
        + 8109252320354666245907324545684805984286) * 10^40
        + 2898018879638657721153554737628069387539)) : ℚ) /
        ((36680 * 10^40
        + 5267114824128922047222362789138794665314) * 10^40
        + 902751818529719531373343041126400000000)),
    (((-875774620147323865939848151) : ℚ) /
        1844674407370955161600000000))

def pairedN02701PlusP002Center2553 : RatPair2542 := ((((-168036782698919993429) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-252698714645137902289) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def pairedN02701PlusP002Factor2553 : RatPair2542 := ((((-(((((((((((382355156645963870248 * 10^40
        + 9198431700287331067129202483757177557686) * 10^40
        + 5559421755990202111642262121049625213252) * 10^40
        + 7844222614577785498787837881020976272919) * 10^40
        + 1490680405997858722113587101229700041503) * 10^40
        + 9854428140953068136887794725484146192031) * 10^40
        + 8271181335912397120878088169226463991599) * 10^40
        + 4521422888907200268495721591710605693256) * 10^40
        + 9747484209752779978706972354089106670748) * 10^40
        + 5640942621230561687489403472890745262200) * 10^40
        + 6675635950261199039421512736244144603830) * 10^40
        + 558866518107198955015590475251627155387)) : ℚ) /
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
    ((((((((((1507735178971 * 10^40
        + 5200677081867397231560240192949787852493) * 10^40
        + 6564029210554965721597939193523051196342) * 10^40
        + 552296670702065043325689673898092059486) * 10^40
        + 3752217662257401901624538025697093522548) * 10^40
        + 2789477634451938732817983192936655836997) * 10^40
        + 227893249482081899402335871848817283775) * 10^40
        + 5838231550294363411688863962504918434538) * 10^40
        + 2904876223758320375132460350013086271723) : ℚ) /
        ((((((((10685920 * 10^40
        + 8698626573180637225289470245261943687371) * 10^40
        + 4854664925507741346767746110602685453773) * 10^40
        + 8948137748171180319286033348791544416498) * 10^40
        + 45943021343597819906620002252686948939) * 10^40
        + 2695148327310254383957658387883810823093) * 10^40
        + 3423061642949699721752439843960503724256) * 10^40
        + 5759831459438283503857105702531114993435) * 10^40
        + 1798758157118995008057425425787038728192)))

noncomputable def pairedN02701PlusP002Error2553 : ℝ := ((2260016183526325913 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP002BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP002Center2553‖ ≤ pairedN02701PlusP002Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP002Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP002Input2553]
  have hs : compactExp2547 pairedN02701PlusP002Input2553 8 =
      (pairedN02701PlusP002Center2553, ((2260016183526325913 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP002Input2553 8).2 : ℝ) =
      pairedN02701PlusP002Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP002Error2553]
  have h := compactExp_error2547 pairedN02701PlusP002Input2553 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          pairedN02701PlusP002Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP002Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP002DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP002Factor2553 * embedPair2542 pairedN02701PlusP002Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP002Factor2553 : ℝ) * pairedN02701PlusP002Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP002Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP002Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP002BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP002Factor2553)

def pairedN02701PlusP003Input2553 : RatPair2542 := ((((-((1204018 * 10^40
        + 3199206753711006565389390034201102437777) * 10^40
        + 7349271424128768512973515705970498543953)) : ℚ) /
        ((6644764 * 10^40
        + 348595898346936727630550565694213304645) * 10^40
        + 356964576015918677191939509452800000000)),
    (((-875774620147323865939848151) : ℚ) /
        1844674407370955161600000000))

def pairedN02701PlusP003Center2553 : RatPair2542 := ((((-5788973884569169910793434755) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-4352815604563173678616329029) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def pairedN02701PlusP003Factor2553 : RatPair2542 :=
    ((((-(((((((((((186851243240711480535630032022282573 *
    10^40
        + 1846649520072842760840959477759161459279) * 10^40
        + 6301121117667000716189358274614140543225) * 10^40
        + 620626247051096807325647168190399530378) * 10^40
        + 3421115577503868416940110467001109919120) * 10^40
        + 5314857290555522011881954770110265842887) * 10^40
        + 6352293250482843918979947373891006851497) * 10^40
        + 3644952545006451346282416698611224644875) * 10^40
        + 429883941054756116772114649548133921757) * 10^40
        + 5333020611960000261240160774477080000141) * 10^40
        + 7760695901693156022938749316756770627767) * 10^40
        + 6313703663451222345508488110816292083361)) : ℚ) /
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
    (((-((((((((1250392538386189540765 * 10^40
        + 729461561593902969282083062436326434193) * 10^40
        + 6552652890763157620206801006374463228403) * 10^40
        + 8816043978982570692743455543268589930247) * 10^40
        + 6485189787230674665703243792735601564414) * 10^40
        + 7769615474992937519341008378995211096655) * 10^40
        + 636852443648408548337868197737005010851) * 10^40
        + 3234780762480145039382166395344967311193) * 10^40
        + 672309644015529135275879348784235782671)) : ℚ) /
        ((((((((34523054038309545 * 10^40
        + 8070460829836846567823988656416628066383) * 10^40
        + 4587402166612519557745250159747618326596) * 10^40
        + 7613747391599567274633108774437485695163) * 10^40
        + 9343961057035675497914777333331863985921) * 10^40
        + 4482676832355296082588408153974825262161) * 10^40
        + 2992432219252968330401935066320003582024) * 10^40
        + 1817157221406445207864595536940876164476) * 10^40
        + 3970392011049662611515175051787780489216)))

noncomputable def pairedN02701PlusP003Error2553 : ℝ := ((36476409710489096549727441 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP003BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP003Center2553‖ ≤ pairedN02701PlusP003Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP003Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP003Input2553]
  have hs : compactExp2547 pairedN02701PlusP003Input2553 8 =
      (pairedN02701PlusP003Center2553, ((36476409710489096549727441 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP003Input2553 8).2 : ℝ) =
      pairedN02701PlusP003Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP003Error2553]
  have h := compactExp_error2547 pairedN02701PlusP003Input2553 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          pairedN02701PlusP003Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP003Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP003DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP003Factor2553 * embedPair2542 pairedN02701PlusP003Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP003Factor2553 : ℝ) * pairedN02701PlusP003Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP003Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP003Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP003BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP003Factor2553)

def pairedN02701PlusP004Input2553 : RatPair2542 := ((((-((21030 * 10^40
        + 4978280417753696551825490501735319367009) * 10^40
        + 9100087780138783714176925758135881887539)) : ℚ) /
        ((134028 * 10^40
        + 5763226050861645114137505055527745988340) * 10^40
        + 4359916327702839531373343041126400000000)),
    ((875774620147323865939848151 : ℚ) /
        1844674407370955161600000000))

def pairedN02701PlusP004Center2553 : RatPair2542 := ((((-725790656500916187131713370187) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((4365862355930743774088204387843 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def pairedN02701PlusP004Factor2553 : RatPair2542 := ((((-(((((((((((248415280343108878144892 *
    10^40
        + 6106007954166609826887656457072682516783) * 10^40
        + 1883568890898143529806259109448868344575) * 10^40
        + 8591293253683491854470720022061319189618) * 10^40
        + 9443927985206434526720445504818450115786) * 10^40
        + 5686043619347034834015375838703941013979) * 10^40
        + 4504076935094857298840291324888523465101) * 10^40
        + 4004152242222654956312723615111476803159) * 10^40
        + 8406570177594728632311857893921842056585) * 10^40
        + 99851205907565425792254912929244439829) * 10^40
        + 6415913292770355531987144281329171687969) * 10^40
        + 8070830225132365958797417770173502155387)) : ℚ) /
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
    ((((((((((103126758515416 * 10^40
        + 4189757770484212890848861273991940904776) * 10^40
        + 4470456653376659163387204036049040475402) * 10^40
        + 2701578863480079114613933684471684321072) * 10^40
        + 4235253844402241103238576215368714487032) * 10^40
        + 3661515926969268093341689396532233933775) * 10^40
        + 1901954023737238522544747324704124014620) * 10^40
        + 2665351148452887440247847875879572030058) * 10^40
        + 367611164591919516332306349205663728277) : ℚ) /
        ((((((((1904843580 * 10^40
        + 4824523594531213353034759566469063183137) * 10^40
        + 9203733929667876279931105266675600147748) * 10^40
        + 5546782268739206171043400601465671486465) * 10^40
        + 9000377039929565390305917709883691541199) * 10^40
        + 9386594298950469050406216961415163469388) * 10^40
        + 2757914341002766027590561291455103603396) * 10^40
        + 3989138872955181030968949404074575480103) * 10^40
        + 6185754302836897738911825425787038728192)))

noncomputable def pairedN02701PlusP004Error2553 : ℝ := ((17853934217737043702764082891 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP004BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP004Center2553‖ ≤ pairedN02701PlusP004Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP004Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP004Input2553]
  have hs : compactExp2547 pairedN02701PlusP004Input2553 8 =
      (pairedN02701PlusP004Center2553, ((17853934217737043702764082891 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP004Input2553 8).2 : ℝ) =
      pairedN02701PlusP004Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP004Error2553]
  have h := compactExp_error2547 pairedN02701PlusP004Input2553 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          pairedN02701PlusP004Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP004Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP004DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP004Factor2553 * embedPair2542 pairedN02701PlusP004Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP004Factor2553 : ℝ) * pairedN02701PlusP004Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP004Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP004Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP004BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP004Factor2553)

def pairedN02701PlusP005Center2553 : RatPair2542 := (0, 0)

def pairedN02701PlusP005Factor2553 : RatPair2542 := (0, 0)

noncomputable def pairedN02701PlusP005Error2553 : ℝ := 0

theorem pairedN02701PlusP005Exterior2553 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN02701PlusPosition2553 = 0
        :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |pairedN02701PlusPosition2553| := by
    norm_num [storedWidth, pairedN02701PlusPosition2553]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem pairedN02701PlusP005BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP005Center2553‖ ≤ pairedN02701PlusP005Error2553 := by
  rw [pairedN02701PlusP005Exterior2553]
  norm_num [pairedN02701PlusP005Center2553, pairedN02701PlusP005Error2553,
      pairedN02701PlusZero2553]

theorem pairedN02701PlusP005DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP005Factor2553 * embedPair2542 pairedN02701PlusP005Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP005Factor2553 : ℝ) * pairedN02701PlusP005Error2553 :=
            by
  rw [pairedN02701PlusP005Exterior2553]
  norm_num [pairedN02701PlusP005Factor2553, pairedN02701PlusP005Center2553,
      pairedN02701PlusP005Error2553, pairedN02701PlusZero2553, pairMagnitude2542]

def pairedN02701PlusP006Input2553 : RatPair2542 := ((((-43838019295084218252511359948400647) : ℚ)
    /
        73447401531966028759865753600000000),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP006Center2553 : RatPair2542 := (((483449294895075 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP006Factor2553 : RatPair2542 := ((((((2343786920105742277 * 10^40
        + 903558756015421386172038172888294468270) * 10^40
        + 5889117902286452368887624885919274000279) * 10^40
        + 7567088786133771173865714654463458884643) : ℚ) /
        (((6687330808176 * 10^40
        + 6002578591449565797216574011898289303650) * 10^40
        + 3939425513291405934887286533123709590768) * 10^40
        + 9399380879513689390925717235707671077144)),
    ((0 : ℚ) /
        1))

noncomputable def pairedN02701PlusP006Error2553 : ℝ := ((2446198475405 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP006BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP006Center2553‖ ≤ pairedN02701PlusP006Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP006Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP006Input2553]
  have hs : compactExp2547 pairedN02701PlusP006Input2553 7 =
      (pairedN02701PlusP006Center2553, ((2446198475405 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP006Input2553 7).2 : ℝ) =
      pairedN02701PlusP006Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP006Error2553]
  have h := compactExp_error2547 pairedN02701PlusP006Input2553 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          pairedN02701PlusP006Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP006Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP006DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP006Factor2553 * embedPair2542 pairedN02701PlusP006Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP006Factor2553 : ℝ) * pairedN02701PlusP006Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP006Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP006Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP006BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP006Factor2553)

def pairedN02701PlusP007Input2553 : RatPair2542 := ((((-((1204018 * 10^40
        + 3199206753711006565389390034201102437777) * 10^40
        + 7349271424128768512973515705970498543953)) : ℚ) /
        ((1661191 * 10^40
        + 87148974586734181907637641423553326161) * 10^40
        + 2589241144003979669297984877363200000000)),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP007Center2553 : RatPair2542 := (((163354299886446954699714643 : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP007Factor2553 : RatPair2542 := ((((((((((((((1525816 * 10^40
        + 5012312550318674695305141536681421945456) * 10^40
        + 1582539853982917293762429598631234993608) * 10^40
        + 3247211439476562995424525110388878035046) * 10^40
        + 6296617452812398279313975360761151687986) * 10^40
        + 6819541862386416868134756444286901687574) * 10^40
        + 1416599514299917533964423683181443804897) * 10^40
        + 502224998084462973793230713597493550666) * 10^40
        + 9045282932124459799306982845318740216308) * 10^40
        + 2359197209578144982731341572975889917156) * 10^40
        + 7901036638530970595392904395332997747393) * 10^40
        + 6182130994503904107926561240781441620243) : ℚ) /
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

noncomputable def pairedN02701PlusP007Error2553 : ℝ := ((759335337735088749674751 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem pairedN02701PlusP007BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP007Center2553‖ ≤ pairedN02701PlusP007Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP007Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP007Input2553]
  have hs : compactExp2547 pairedN02701PlusP007Input2553 6 =
      (pairedN02701PlusP007Center2553, ((759335337735088749674751 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP007Input2553 6).2 : ℝ) =
      pairedN02701PlusP007Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP007Error2553]
  have h := compactExp_error2547 pairedN02701PlusP007Input2553 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          pairedN02701PlusP007Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP007Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP007DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP007Factor2553 * embedPair2542 pairedN02701PlusP007Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP007Factor2553 : ℝ) * pairedN02701PlusP007Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP007Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP007Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP007BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP007Factor2553)

def pairedN02701PlusP008Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((630729240492097551551105443 : ℚ) /
        944473296573929042739200000000))

def pairedN02701PlusP008Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP008Factor2553 : RatPair2542 :=
    ((((((((((((((1211860026768282206817236312930105
    * 10^40
        + 4320638676143398784620814928625766274218) * 10^40
        + 7179642908554422000311288613462596412488) * 10^40
        + 516213064235479313855357313095261214717) * 10^40
        + 7561211633502916417898367713589369812766) * 10^40
        + 8231736871759809308896157567756497399126) * 10^40
        + 1071634532720212985623971173312719936669) * 10^40
        + 3319875009784301279065419718274189265940) * 10^40
        + 1954671247522168261181262177907711866583) * 10^40
        + 8175309902295047165870759728327581759376) * 10^40
        + 3696294053461527089545919211564915436146) * 10^40
        + 5352695176940652590318330062991174412551) : ℚ) /
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
    (((-((((((((263628642471852842415 * 10^40
        + 5904146725681829715517824571814474260566) * 10^40
        + 7031264959283221620513416461388217607827) * 10^40
        + 4216670189611915372271857426965278799394) * 10^40
        + 4519756974553681634995812278437433214649) * 10^40
        + 5421842818564593935023759557511532423620) * 10^40
        + 8162281421879466848456326380488749962653) * 10^40
        + 579828190248114614007439164256839131094) * 10^40
        + 2962345461194840705859574020854864849693)) : ℚ) /
        ((((((((7729 * 10^40
        + 4837318072590597840552870501097756850724) * 10^40
        + 4781501533621654299657649497215044513448) * 10^40
        + 9563377623048415760176099549591302788187) * 10^40
        + 1000664459254159763726137558544413714928) * 10^40
        + 8372752059637550852644505599220433275192) * 10^40
        + 3343940703284548809449863170981759854536) * 10^40
        + 5017529300504592352749711117348899791699) * 10^40
        + 4807389080660183792171320414302243913728)))

noncomputable def pairedN02701PlusP008Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP008BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP008Center2553‖ ≤ pairedN02701PlusP008Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP008Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP008Input2553]
  have hs : compactExp2547 pairedN02701PlusP008Input2553 16 =
      (pairedN02701PlusP008Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP008Input2553 16).2 : ℝ) =
      pairedN02701PlusP008Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP008Error2553]
  have h := compactExp_error2547 pairedN02701PlusP008Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP008Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP008Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP008DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP008Factor2553 * embedPair2542 pairedN02701PlusP008Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP008Factor2553 : ℝ) * pairedN02701PlusP008Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP008Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP008Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP008BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP008Factor2553)

def pairedN02701PlusP009Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((938059634128117561826070909 : ℚ) /
        944473296573929042739200000000))

def pairedN02701PlusP009Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP009Factor2553 : RatPair2542 :=
    ((((((((((((((1211860026767187628331781176054147
    * 10^40
        + 3358671831645475033031497332694751701729) * 10^40
        + 328695552165477821682631662513421133417) * 10^40
        + 9452463407726432360984136400900824170617) * 10^40
        + 8695324294518527209968703242840492901213) * 10^40
        + 2721118827376756433764848623304749943835) * 10^40
        + 185793181944046496034533606219481456325) * 10^40
        + 8724490929025741848623818457254641396468) * 10^40
        + 6052151519255022118477797154920575455167) * 10^40
        + 6150785033125122047546920415217945789722) * 10^40
        + 5534206252770368534142036485570895111519) * 10^40
        + 8441550699910012112303489356537615324103) : ℚ) /
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
    (((-((((((((130694954362070257331 * 10^40
        + 8074285647291923400154698094268317588295) * 10^40
        + 1203907423733392739956763495178773104024) * 10^40
        + 9026043242229086796999583673785456814025) * 10^40
        + 5851272893945820215154451098023402634795) * 10^40
        + 8728288924307839179693825422312456549858) * 10^40
        + 9467598969207626827643290109115580324005) * 10^40
        + 5117187010117935422932893800700622480820) * 10^40
        + 69149983117235699238166213910582774401)) : ℚ) /
        ((((((((2576 * 10^40
        + 4945772690863532613517623500365918950241) * 10^40
        + 4927167177873884766552549832405014837816) * 10^40
        + 3187792541016138586725366516530434262729) * 10^40
        + 333554819751386587908712519514804571642) * 10^40
        + 9457584019879183617548168533073477758397) * 10^40
        + 4447980234428182936483287723660586618178) * 10^40
        + 8339176433501530784249903705782966597233) * 10^40
        + 1602463026886727930723773471434081304576)))

noncomputable def pairedN02701PlusP009Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP009BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP009Center2553‖ ≤ pairedN02701PlusP009Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP009Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP009Input2553]
  have hs : compactExp2547 pairedN02701PlusP009Input2553 16 =
      (pairedN02701PlusP009Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP009Input2553 16).2 : ℝ) =
      pairedN02701PlusP009Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP009Error2553]
  have h := compactExp_error2547 pairedN02701PlusP009Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP009Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP009Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP009DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP009Factor2553 * embedPair2542 pairedN02701PlusP009Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP009Factor2553 : ℝ) * pairedN02701PlusP009Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP009Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP009Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP009BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP009Factor2553)

def pairedN02701PlusP010Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((558025679572758329216722299 : ℚ) /
        472236648286964521369600000000))

def pairedN02701PlusP010Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP010Factor2553 : RatPair2542 :=
    ((((((((((((((302965006691589396322363684006409
    * 10^40
        + 9923232271913311976655530388471042978374) * 10^40
        + 5829412907983555784531148791556264650205) * 10^40
        + 2412085579620547567037414372593605132078) * 10^40
        + 7925029201068093531939005163662433725876) * 10^40
        + 9252709307251256440652724345122800805165) * 10^40
        + 3469631527920901327955859414407106919014) * 10^40
        + 5311828693811618045097715937920765642087) * 10^40
        + 1509105016404491585075255399811437711309) * 10^40
        + 9332423344282144647153759232287875097441) * 10^40
        + 2490688639861007380369754997732700950867) * 10^40
        + 1695211690050536535077458750287743469239) : ℚ) /
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
    (((-((((((((19436701588914817835 * 10^40
        + 6342047899477487383684977037624033995985) * 10^40
        + 3728499022207029519919808970993670616400) * 10^40
        + 3322539631641942803538522893534508652135) * 10^40
        + 1673880413441155479495489630750924453200) * 10^40
        + 3015332479612597231384556534871996082480) * 10^40
        + 718161673513979906407038863049010701333) * 10^40
        + 5907862612022075807859907171926586886609) * 10^40
        + 1016371900726376387950795756280718180807)) : ℚ) /
        ((((((((322 * 10^40
        + 618221586357941576689702937545739868780) * 10^40
        + 1865895897234235595819068729050626854727) * 10^40
        + 398474067627017323340670814566304282841) * 10^40
        + 1291694352468923323488589064939350571455) * 10^40
        + 3682198002484897952193521066634184719799) * 10^40
        + 6805997529303522867060410965457573327272) * 10^40
        + 3542397054187691348031237963222870824654) * 10^40
        + 1450307878360840991340471683929260163072)))

noncomputable def pairedN02701PlusP010Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP010BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP010Center2553‖ ≤ pairedN02701PlusP010Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP010Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP010Input2553]
  have hs : compactExp2547 pairedN02701PlusP010Input2553 16 =
      (pairedN02701PlusP010Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP010Input2553 16).2 : ℝ) =
      pairedN02701PlusP010Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP010Error2553]
  have h := compactExp_error2547 pairedN02701PlusP010Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP010Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP010Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP010DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP010Factor2553 * embedPair2542 pairedN02701PlusP010Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP010Factor2553 : ℝ) * pairedN02701PlusP010Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP010Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP010Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP010BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP010Factor2553)

def pairedN02701PlusP011Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((617361885721254929729880619 : ℚ) /
        472236648286964521369600000000))

def pairedN02701PlusP011Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP011Factor2553 : RatPair2542 :=
    ((((((((((((((302965006691431061017959688419675
    * 10^40
        + 9463381124148114159543591089687367259103) * 10^40
        + 9634294588548537480493656448556574999941) * 10^40
        + 9718814803429473499366739880443134683854) * 10^40
        + 5987248101714093028884061193961874549338) * 10^40
        + 5650904253554671719359397418131539611427) * 10^40
        + 701976691269701962158282103515108515918) * 10^40
        + 9906277502905732444014111657459445520197) * 10^40
        + 6764690315973380155999677123159949035269) * 10^40
        + 5714628974713104512659616832261298301351) * 10^40
        + 4296999945254341608651794406703456928059) * 10^40
        + 1354528006761911034985921555246137640599) : ℚ) /
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
    (((-((((((((64510357772353262539 * 10^40
        + 290328058517051659951754001759238820313) * 10^40
        + 9986901130420020799939341854024578294415) * 10^40
        + 1638924106267903540704671444369202384380) * 10^40
        + 6308465692383939732802058596397153792418) * 10^40
        + 2561001607047678203383675271632940727631) * 10^40
        + 5709240849994712165622022898540470408021) * 10^40
        + 6713513793307725206185849098089347045152) * 10^40
        + 6871035927415773147974120188342589060421)) : ℚ) /
        ((((((((966 * 10^40
        + 1854664759073824730069108812637219606340) * 10^40
        + 5597687691702706787457206187151880564181) * 10^40
        + 1195422202881051970022012443698912848523) * 10^40
        + 3875083057406769970465767194818051714366) * 10^40
        + 1046594007454693856580563199902554159399) * 10^40
        + 417992587910568601181232896372719981817) * 10^40
        + 627191162563074044093713889668612473962) * 10^40
        + 4350923635082522974021415051787780489216)))

noncomputable def pairedN02701PlusP011Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP011BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP011Center2553‖ ≤ pairedN02701PlusP011Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP011Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP011Input2553]
  have hs : compactExp2547 pairedN02701PlusP011Input2553 16 =
      (pairedN02701PlusP011Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP011Input2553 16).2 : ℝ) =
      pairedN02701PlusP011Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP011Error2553]
  have h := compactExp_error2547 pairedN02701PlusP011Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP011Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP011Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP011DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP011Factor2553 * embedPair2542 pairedN02701PlusP011Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP011Factor2553 : ℝ) * pairedN02701PlusP011Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP011Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP011Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP011BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP011Factor2553)

def pairedN02701PlusP012Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((13576393469632358173878271 : ℚ) /
        9444732965739290427392000000))

def pairedN02701PlusP012Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP012Factor2553 : RatPair2542 := ((((((((((((((75741251672812552635471355095677
    *
    10^40
        + 5086600394362185258041833065638256944465) * 10^40
        + 6211655465857111443639033961407334532220) * 10^40
        + 9815019072512980822233129260126547741316) * 10^40
        + 5821612938152118399857164922291654592285) * 10^40
        + 7405554398110314180244443198106388680245) * 10^40
        + 6801045521162466088037511399419932691655) * 10^40
        + 8778958731354514937690079863338630967776) * 10^40
        + 6901828437791568080667884108147149063997) * 10^40
        + 652772808267590109269204444762072652369) * 10^40
        + 2190595180661289933901852358296736326322) * 10^40
        + 3218514869234841677398277337323860035807) : ℚ) /
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
    (((-((((((((8866537806275491225 * 10^40
        + 1202233336386157670037651364635676562904) * 10^40
        + 6116334355595760648418002065540519054834) * 10^40
        + 9399300388304309978673847724257746855213) * 10^40
        + 2497780866101333409944413340738312136675) * 10^40
        + 5098569807527825197451626778004294553971) * 10^40
        + 1807708083745199182419628517118863476373) * 10^40
        + 5569386697859078933416358556741290289852) * 10^40
        + 5951408537381936877412786006291037780225)) : ℚ) /
        ((((((((120 * 10^40
        + 7731833094884228091258638601579652450792) * 10^40
        + 5699710961462838348432150773393985070522) * 10^40
        + 6399427775360131496252751555462364106065) * 10^40
        + 4234385382175846246308220899352256464295) * 10^40
        + 7630824250931836732072570399987819269924) * 10^40
        + 8802249073488821075147654112046589997727) * 10^40
        + 1328398895320384255511714236208576559245) * 10^40
        + 3043865454385315371752676881473472561152)))

noncomputable def pairedN02701PlusP012Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP012BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP012Center2553‖ ≤ pairedN02701PlusP012Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP012Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP012Input2553]
  have hs : compactExp2547 pairedN02701PlusP012Input2553 16 =
      (pairedN02701PlusP012Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP012Input2553 16).2 : ℝ) =
      pairedN02701PlusP012Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP012Error2553]
  have h := compactExp_error2547 pairedN02701PlusP012Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP012Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP012Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP012DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP012Factor2553 * embedPair2542 pairedN02701PlusP012Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP012Factor2553 : ℝ) * pairedN02701PlusP012Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP012Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP012Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP012BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP012Factor2553)

def pairedN02701PlusP013Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((146965053600227290725850929 : ℚ) /
        94447329657392904273920000000))

def pairedN02701PlusP013Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP013Factor2553 : RatPair2542 :=
    ((((((((((((((302965006691070468922628188221896
    * 10^40
        + 2730472537748493623349493731827016262736) * 10^40
        + 4267972439801133039860585120815182879592) * 10^40
        + 8989997443531998693994592213413794213671) * 10^40
        + 7230136935695688328269747209010637579192) * 10^40
        + 9044883338256661522427672683637258378294) * 10^40
        + 5498905059746539548876268543588319378049) * 10^40
        + 978382979215666891041374707671540045957) * 10^40
        + 6340960303440156840953785607609582879415) * 10^40
        + 2405057940702753919691911175896387670039) * 10^40
        + 9919044824998230748071399088260968708452) * 10^40
        + 2027275535582452833791088815092195804503) : ℚ) /
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
    (((-((((((((25594842633523445022 * 10^40
        + 5067613688924179355667099072885487627655) * 10^40
        + 8910734633938391343554748848670459721903) * 10^40
        + 9985358197600839004711954172419026207417) * 10^40
        + 915724275469161711508359649237196221802) * 10^40
        + 8464066482544998431912654466923490562169) * 10^40
        + 1292630626744625756265844586981976309116) * 10^40
        + 4907043754451393271391807851251849785520) * 10^40
        + 7857062854727880304978940833400972325065)) : ℚ) /
        ((((((((322 * 10^40
        + 618221586357941576689702937545739868780) * 10^40
        + 1865895897234235595819068729050626854727) * 10^40
        + 398474067627017323340670814566304282841) * 10^40
        + 1291694352468923323488589064939350571455) * 10^40
        + 3682198002484897952193521066634184719799) * 10^40
        + 6805997529303522867060410965457573327272) * 10^40
        + 3542397054187691348031237963222870824654) * 10^40
        + 1450307878360840991340471683929260163072)))

noncomputable def pairedN02701PlusP013Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP013BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP013Center2553‖ ≤ pairedN02701PlusP013Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP013Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP013Input2553]
  have hs : compactExp2547 pairedN02701PlusP013Input2553 16 =
      (pairedN02701PlusP013Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP013Input2553 16).2 : ℝ) =
      pairedN02701PlusP013Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP013Error2553]
  have h := compactExp_error2547 pairedN02701PlusP013Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP013Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP013Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP013DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP013Factor2553 * embedPair2542 pairedN02701PlusP013Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP013Factor2553 : ℝ) * pairedN02701PlusP013Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP013Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP013Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP013BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP013Factor2553)

def pairedN02701PlusP014Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((838597898629083505249081609 : ℚ) /
        472236648286964521369600000000))

def pairedN02701PlusP014Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP014Factor2553 : RatPair2542 :=
    ((((((((((((((302965006690699783710336804150780
    * 10^40
        + 7375798959939785699446121107280914445249) * 10^40
        + 3097561911124212377258681995077095254509) * 10^40
        + 2229014319779603077059181860794967246633) * 10^40
        + 9947679788910352715194764290800335306938) * 10^40
        + 6993718228039765426504386223723496379952) * 10^40
        + 1137580772574304972720075781333851205189) * 10^40
        + 6589400949575182239445010583185685093925) * 10^40
        + 1640222674287998251561042056717936327050) * 10^40
        + 1807234477333822545609498080574094550070) * 10^40
        + 5637447982941451076858890916691237047606) * 10^40
        + 8988031878629068926281861861910580555519) : ℚ) /
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
    (((-((((((((87628102283135121880 * 10^40
        + 2833343307881745304287864557445329429772) * 10^40
        + 4852140968381167843448143940477339610116) * 10^40
        + 3312858595759646183790046152538106073446) * 10^40
        + 883685594106097231993023233935762280767) * 10^40
        + 147237014340899310436599037953626776481) * 10^40
        + 7125599577129098828177232695776761390625) * 10^40
        + 5237300570860112427296195705482550746159) * 10^40
        + 621454128577929948293605922241172177071)) : ℚ) /
        ((((((((966 * 10^40
        + 1854664759073824730069108812637219606340) * 10^40
        + 5597687691702706787457206187151880564181) * 10^40
        + 1195422202881051970022012443698912848523) * 10^40
        + 3875083057406769970465767194818051714366) * 10^40
        + 1046594007454693856580563199902554159399) * 10^40
        + 417992587910568601181232896372719981817) * 10^40
        + 627191162563074044093713889668612473962) * 10^40
        + 4350923635082522974021415051787780489216)))

noncomputable def pairedN02701PlusP014Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP014BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP014Center2553‖ ≤ pairedN02701PlusP014Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP014Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP014Input2553]
  have hs : compactExp2547 pairedN02701PlusP014Input2553 16 =
      (pairedN02701PlusP014Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP014Input2553 16).2 : ℝ) =
      pairedN02701PlusP014Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP014Error2553]
  have h := compactExp_error2547 pairedN02701PlusP014Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP014Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP014Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP014DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP014Factor2553 * embedPair2542 pairedN02701PlusP014Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP014Factor2553 : ℝ) * pairedN02701PlusP014Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP014Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP014Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP014BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP014Factor2553)

def pairedN02701PlusP015Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((912951341665564226630614693 : ℚ) /
        472236648286964521369600000000))

def pairedN02701PlusP015Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP015Factor2553 : RatPair2542 :=
    ((((((((((((((302965006690404118429569397219452
    * 10^40
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

noncomputable def pairedN02701PlusP015Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP015BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP015Center2553‖ ≤ pairedN02701PlusP015Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP015Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP015Input2553]
  have hs : compactExp2547 pairedN02701PlusP015Input2553 16 =
      (pairedN02701PlusP015Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP015Input2553 16).2 : ℝ) =
      pairedN02701PlusP015Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP015Error2553]
  have h := compactExp_error2547 pairedN02701PlusP015Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP015Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP015Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP015DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP015Factor2553 * embedPair2542 pairedN02701PlusP015Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP015Factor2553 : ℝ) * pairedN02701PlusP015Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP015Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP015Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP015BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP015Factor2553)

def pairedN02701PlusP016Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((483342473044070207188278171 : ℚ) /
        236118324143482260684800000000))

def pairedN02701PlusP016Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP016Factor2553 : RatPair2542 := ((((((((((((((75741251672543705579602600368318
    *
    10^40
        + 26643090655849766769440171414144474609) * 10^40
        + 3763350163425586476541501061381609663524) * 10^40
        + 4559572561303734014960420906580691452998) * 10^40
        + 3546832343771934553569971705963069535542) * 10^40
        + 575688300445717144775520246434478584783) * 10^40
        + 1889819653806978852789690511960068638439) * 10^40
        + 4410712716587050355976585523679076950975) * 10^40
        + 6369442216023349394760872977241182067408) * 10^40
        + 649125491748136853466969629174602555079) * 10^40
        + 5885441146190797523733152074447989202485) * 10^40
        + 7272744940657838584204130747356820872183) : ℚ) /
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
    (((-((((((((4208849053771865142 * 10^40
        + 2877241191059458248348529658706953324268) * 10^40
        + 1794188684475874438069005849356877816540) * 10^40
        + 388106700421257740830183572109725059527) * 10^40
        + 8423328065932123932555404197564832190256) * 10^40
        + 5861724873150583226071277085519630376535) * 10^40
        + 6183978167040434918174333480431528351954) * 10^40
        + 6907305180468789974345573501518674541020) * 10^40
        + 1965862067973893806846586835732710133159)) : ℚ) /
        ((((((((40 * 10^40
        + 2577277698294742697086212867193217483597) * 10^40
        + 5233236987154279449477383591131328356840) * 10^40
        + 8799809258453377165417583851820788035355) * 10^40
        + 1411461794058615415436073633117418821431) * 10^40
        + 9210274750310612244024190133329273089974) * 10^40
        + 9600749691162940358382551370682196665909) * 10^40
        + 442799631773461418503904745402858853081) * 10^40
        + 7681288484795105123917558960491157520384)))

noncomputable def pairedN02701PlusP016Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP016BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP016Center2553‖ ≤ pairedN02701PlusP016Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP016Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP016Input2553]
  have hs : compactExp2547 pairedN02701PlusP016Input2553 16 =
      (pairedN02701PlusP016Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP016Input2553 16).2 : ℝ) =
      pairedN02701PlusP016Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP016Error2553]
  have h := compactExp_error2547 pairedN02701PlusP016Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP016Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP016Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP016DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP016Factor2553 * embedPair2542 pairedN02701PlusP016Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP016Factor2553 : ℝ) * pairedN02701PlusP016Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP016Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP016Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP016BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP016Factor2553)

def pairedN02701PlusP017Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1071059113331693339029979313 : ℚ) /
        472236648286964521369600000000))

def pairedN02701PlusP017Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP017Factor2553 : RatPair2542 :=
    ((((((((((((((302965006689691964182124674900318
    * 10^40
        + 7922573286633823662285352010694161261112) * 10^40
        + 2081460176378309982413553235995774658712) * 10^40
        + 340114564159724537233252984200647104762) * 10^40
        + 7235034757493941756266610477779627677126) * 10^40
        + 9832388333791797260511442013071132486254) * 10^40
        + 2571702861748638818744349943622164662715) * 10^40
        + 5065157257151261046612079292197394113775) * 10^40
        + 1269606312584396483727162248060390524010) * 10^40
        + 7871639231995222845453508720567179331400) * 10^40
        + 6671883344397898076307824709201473619694) * 10^40
        + 8090841804642378834365645660388257250287) : ℚ) /
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
    (((-((((((((37306269463871497345 * 10^40
        + 6763275734560701326893853047703020757988) * 10^40
        + 2476529465383260103759279144059198075332) * 10^40
        + 5049233959999837858279003517848501291142) * 10^40
        + 7228239566453069866442317655552592136446) * 10^40
        + 819978173644626006176127226372295919104) * 10^40
        + 683691627272175756420344932700841278453) * 10^40
        + 9669687005770812652205748274067065573173) * 10^40
        + 9657526483176677364613569119665919920573)) : ℚ) /
        ((((((((322 * 10^40
        + 618221586357941576689702937545739868780) * 10^40
        + 1865895897234235595819068729050626854727) * 10^40
        + 398474067627017323340670814566304282841) * 10^40
        + 1291694352468923323488589064939350571455) * 10^40
        + 3682198002484897952193521066634184719799) * 10^40
        + 6805997529303522867060410965457573327272) * 10^40
        + 3542397054187691348031237963222870824654) * 10^40
        + 1450307878360840991340471683929260163072)))

noncomputable def pairedN02701PlusP017Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP017BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP017Center2553‖ ≤ pairedN02701PlusP017Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP017Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP017Input2553]
  have hs : compactExp2547 pairedN02701PlusP017Input2553 16 =
      (pairedN02701PlusP017Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP017Input2553 16).2 : ℝ) =
      pairedN02701PlusP017Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP017Error2553]
  have h := compactExp_error2547 pairedN02701PlusP017Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP017Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP017Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP017DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP017Factor2553 * embedPair2542 pairedN02701PlusP017Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP017Factor2553 : ℝ) * pairedN02701PlusP017Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP017Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP017Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP017BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP017Factor2553)

def pairedN02701PlusP018Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((277630191250842385602313847 : ℚ) /
        118059162071741130342400000000))

def pairedN02701PlusP018Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP018Factor2553 : RatPair2542 := ((((((((((((((18935312918093532485220003986964
    *
    10^40
        + 6073739943902541274643533307951388977566) * 10^40
        + 7391166176124890771264049185061605231300) * 10^40
        + 6793027120091178746669199061387394746140) * 10^40
        + 784564548514719010526953364409643092856) * 10^40
        + 3355808698323843523479516901314337038563) * 10^40
        + 9189534955022477031604928569906766216261) * 10^40
        + 4771571238945097767324243469116851345898) * 10^40
        + 7850674152830302690294518340854746402896) * 10^40
        + 4464645802306128416548726689729043831078) * 10^40
        + 4099911606152932012565402209991794275282) * 10^40
        + 5458688766191895829001178867043052267007) : ℚ) /
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
    (((-((((((((1813160904914584406 * 10^40
        + 8288204275205695233430037282452303490655) * 10^40
        + 1257554870714714561759505772443475910689) * 10^40
        + 583439330895028627402980496268697349026) * 10^40
        + 8772784011737316929791901099957307914748) * 10^40
        + 555014288829350089251686309433109900691) * 10^40
        + 5858844229870763100403531225793042672172) * 10^40
        + 8392048168706027172826313709931225993217) * 10^40
        + 4829030301128575826981830775891717031121)) : ℚ) /
        ((((((((15 * 10^40
        + 966479136860528511407329825197456556349) * 10^40
        + 712463870182854793554018846674248133815) * 10^40
        + 3299928471920016437031593944432795513258) * 10^40
        + 1779298172771980780788527612419032058036) * 10^40
        + 9703853031366479591509071299998477408740) * 10^40
        + 6100281134186102634393456764005823749715) * 10^40
        + 8916049861915048031938964279526072069905) * 10^40
        + 6630483181798164421469084610184184070144)))

noncomputable def pairedN02701PlusP018Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP018BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP018Center2553‖ ≤ pairedN02701PlusP018Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP018Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP018Input2553]
  have hs : compactExp2547 pairedN02701PlusP018Input2553 16 =
      (pairedN02701PlusP018Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP018Input2553 16).2 : ℝ) =
      pairedN02701PlusP018Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP018Error2553]
  have h := compactExp_error2547 pairedN02701PlusP018Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP018Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP018Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP018DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP018Factor2553 * embedPair2542 pairedN02701PlusP018Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP018Factor2553 : ℝ) * pairedN02701PlusP018Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP018Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP018Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP018BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP018Factor2553)

def pairedN02701PlusP019Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((59091935462568230097122829 : ℚ) /
        23611832414348226068480000000))

def pairedN02701PlusP019Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP019Factor2553 : RatPair2542 := ((((((((((((((18935312918070335131214258380944
    *
    10^40
        + 4936052978456437625057992207793858274196) * 10^40
        + 2874689580441881830398327580452311830523) * 10^40
        + 6795834416739834053122856563208499202299) * 10^40
        + 8819322043832725389775049085833005084828) * 10^40
        + 3567379126947688393605753769972549791119) * 10^40
        + 9778219474703528913134315213871489796686) * 10^40
        + 646469387323195140527254694939493049161) * 10^40
        + 7286259644695243525551606064363653979809) * 10^40
        + 7224573679835467178807259091050304647354) * 10^40
        + 8362881058660419634949460407736539540056) * 10^40
        + 8042248557717513498670337790807198610383) : ℚ) /
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
    (((-((((((((643200863072108674 * 10^40
        + 6222435015043348654644504097167859861353) * 10^40
        + 3669568175925893255216196962173015282395) * 10^40
        + 7154419350130813755703777603741641729376) * 10^40
        + 8507311500692732089773309463931325222269) * 10^40
        + 9448104212523622822382421678948228447572) * 10^40
        + 4732134706546921008243037426805920852334) * 10^40
        + 1437058171969317845177592688515765650219) * 10^40
        + 5997280901403677111343558499779906753965)) : ℚ) /
        ((((((((5 * 10^40
        + 322159712286842837135776608399152185449) * 10^40
        + 6904154623394284931184672948891416044605) * 10^40
        + 1099976157306672145677197981477598504419) * 10^40
        + 3926432724257326926929509204139677352678) * 10^40
        + 9901284343788826530503023766666159136246) * 10^40
        + 8700093711395367544797818921335274583238) * 10^40
        + 6305349953971682677312988093175357356635) * 10^40
        + 2210161060599388140489694870061394690048)))

noncomputable def pairedN02701PlusP019Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP019BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP019Center2553‖ ≤ pairedN02701PlusP019Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP019Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP019Input2553]
  have hs : compactExp2547 pairedN02701PlusP019Input2553 16 =
      (pairedN02701PlusP019Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP019Input2553 16).2 : ℝ) =
      pairedN02701PlusP019Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP019Error2553]
  have h := compactExp_error2547 pairedN02701PlusP019Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP019Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP019Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP019DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP019Factor2553 * embedPair2542 pairedN02701PlusP019Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP019Factor2553 : ℝ) * pairedN02701PlusP019Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP019Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP019Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP019BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP019Factor2553)

def pairedN02701PlusP020Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1259391271552815101014882561 : ℚ) /
        472236648286964521369600000000))

def pairedN02701PlusP020Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP020Factor2553 : RatPair2542 :=
    ((((((((((((((302965006688695546928186678240026
    * 10^40
        + 8708904552605764943856610552614080341866) * 10^40
        + 8033416790395313115876159892453742993769) * 10^40
        + 8365202258623203070750453689489900940662) * 10^40
        + 5596866795844702638733098656899635812757) * 10^40
        + 8111512818179587457871007574536764734318) * 10^40
        + 7007871086236334842869694758944023762105) * 10^40
        + 7823703071281546717574266317387412871487) * 10^40
        + 1109582725782332984945989607446336482507) * 10^40
        + 2158492614216396073837928617406439422224) * 10^40
        + 5496455261530138410201060587477282871038) * 10^40
        + 3693021173262724383307341900321486087759) : ℚ) /
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
    (((-((((((((131598311107679696519 * 10^40
        + 6754647537902876739210325784927620359662) * 10^40
        + 846205169814672912415248019473944895969) * 10^40
        + 6965469036296151221758093551940404418729) * 10^40
        + 4054103134808865022066651414029313981056) * 10^40
        + 4165680867770998197815205232096673717581) * 10^40
        + 2530659064943337505842342171107562107402) * 10^40
        + 9436729798039661183346316499931575050183) * 10^40
        + 8198339688356448137368978356055640302279)) : ℚ) /
        ((((((((966 * 10^40
        + 1854664759073824730069108812637219606340) * 10^40
        + 5597687691702706787457206187151880564181) * 10^40
        + 1195422202881051970022012443698912848523) * 10^40
        + 3875083057406769970465767194818051714366) * 10^40
        + 1046594007454693856580563199902554159399) * 10^40
        + 417992587910568601181232896372719981817) * 10^40
        + 627191162563074044093713889668612473962) * 10^40
        + 4350923635082522974021415051787780489216)))

noncomputable def pairedN02701PlusP020Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP020BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP020Center2553‖ ≤ pairedN02701PlusP020Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP020Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP020Input2553]
  have hs : compactExp2547 pairedN02701PlusP020Input2553 16 =
      (pairedN02701PlusP020Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP020Input2553 16).2 : ℝ) =
      pairedN02701PlusP020Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP020Error2553]
  have h := compactExp_error2547 pairedN02701PlusP020Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP020Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP020Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP020DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP020Factor2553 * embedPair2542 pairedN02701PlusP020Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP020Factor2553 : ℝ) * pairedN02701PlusP020Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP020Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP020Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP020BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP020Factor2553)

def pairedN02701PlusP021Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1324111916357314294844085153 : ℚ) /
        472236648286964521369600000000))

def pairedN02701PlusP021Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP021Factor2553 : RatPair2542 :=
    ((((((((((((((302965006688315944718489138650005
    * 10^40
        + 4433169501639640018041818064302420620379) * 10^40
        + 8011920863521915247707232831220748731769) * 10^40
        + 9939262994716893350208966544654819319307) * 10^40
        + 293970992572048312450568775532860119231) * 10^40
        + 5358332636516460531113208250610249148765) * 10^40
        + 803774273497791094424504076404050083481) * 10^40
        + 6489855913440450817976936408802075724184) * 10^40
        + 4346576677456091359873621656058384748790) * 10^40
        + 2185574117219011720283839307487099236097) * 10^40
        + 2448173862571568989160785736539061726732) * 10^40
        + 2378601124516934011892432775658163450127) : ℚ) /
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
    (((-((((((((46120401140386439989 * 10^40
        + 1047069168230912821241648888328030449036) * 10^40
        + 833798293437385045981796108672329172011) * 10^40
        + 1460692550533544300534844602825565551686) * 10^40
        + 1466416097619058398497824839102632644976) * 10^40
        + 6832508006755854920375593600498265891964) * 10^40
        + 3929374000293436559637559094937394740233) * 10^40
        + 7948476616188455043828562358242748441773) * 10^40
        + 3767658569453792492921977654057556569933)) : ℚ) /
        ((((((((322 * 10^40
        + 618221586357941576689702937545739868780) * 10^40
        + 1865895897234235595819068729050626854727) * 10^40
        + 398474067627017323340670814566304282841) * 10^40
        + 1291694352468923323488589064939350571455) * 10^40
        + 3682198002484897952193521066634184719799) * 10^40
        + 6805997529303522867060410965457573327272) * 10^40
        + 3542397054187691348031237963222870824654) * 10^40
        + 1450307878360840991340471683929260163072)))

noncomputable def pairedN02701PlusP021Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP021BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP021Center2553‖ ≤ pairedN02701PlusP021Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP021Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP021Input2553]
  have hs : compactExp2547 pairedN02701PlusP021Input2553 16 =
      (pairedN02701PlusP021Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP021Input2553 16).2 : ℝ) =
      pairedN02701PlusP021Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP021Error2553]
  have h := compactExp_error2547 pairedN02701PlusP021Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP021Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP021Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP021DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP021Factor2553 * embedPair2542 pairedN02701PlusP021Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP021Factor2553 : ℝ) * pairedN02701PlusP021Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP021Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP021Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP021BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP021Factor2553)

def pairedN02701PlusP022Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((271447665815041436069447627 : ℚ) /
        94447329657392904273920000000))

def pairedN02701PlusP022Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP022Factor2553 : RatPair2542 :=
    ((((((((((((((302965006688114291643264429169795
    * 10^40
        + 9127636245966244600858983575475207975229) * 10^40
        + 9423768590740818373339115953544609518824) * 10^40
        + 5697516888567279345955962412533118231122) * 10^40
        + 928299081813695662230303349643000629203) * 10^40
        + 2549885570391365580585395832255276630370) * 10^40
        + 1637926978103545677206564423699573656981) * 10^40
        + 8746350045313220044434965869366679264767) * 10^40
        + 2452627435612731870559293445557295226363) * 10^40
        + 7832487965741133918725125870225491310124) * 10^40
        + 2475142865280937582245384216500494772119) * 10^40
        + 655368108721709561367553863960683048703) : ℚ) /
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
    (((-((((((((141822701102766867424 * 10^40
        + 9620762949407487024915931860964508390020) * 10^40
        + 3328484139063731983438956767891041406185) * 10^40
        + 3765310073356744772846021914767096623499) * 10^40
        + 2779541425235958661908873805680202544033) * 10^40
        + 309128752655065747528363975404850237273) * 10^40
        + 7414245267367269978479147008126794907503) * 10^40
        + 1795949278422383828594167592671009858136) * 10^40
        + 3936577368566638596204233347416040488785)) : ℚ) /
        ((((((((966 * 10^40
        + 1854664759073824730069108812637219606340) * 10^40
        + 5597687691702706787457206187151880564181) * 10^40
        + 1195422202881051970022012443698912848523) * 10^40
        + 3875083057406769970465767194818051714366) * 10^40
        + 1046594007454693856580563199902554159399) * 10^40
        + 417992587910568601181232896372719981817) * 10^40
        + 627191162563074044093713889668612473962) * 10^40
        + 4350923635082522974021415051787780489216)))

noncomputable def pairedN02701PlusP022Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP022BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP022Center2553‖ ≤ pairedN02701PlusP022Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP022Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP022Input2553]
  have hs : compactExp2547 pairedN02701PlusP022Input2553 16 =
      (pairedN02701PlusP022Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP022Input2553 16).2 : ℝ) =
      pairedN02701PlusP022Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP022Error2553]
  have h := compactExp_error2547 pairedN02701PlusP022Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP022Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP022Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP022DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP022Factor2553 * embedPair2542 pairedN02701PlusP022Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP022Factor2553 : ℝ) * pairedN02701PlusP022Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP022Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP022Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP022BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP022Factor2553)

def pairedN02701PlusP023Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((726373966280652557447321527 : ℚ) /
        236118324143482260684800000000))

def pairedN02701PlusP023Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP023Factor2553 : RatPair2542 := ((((((((((((((75741251671876248978772881192326
    *
    10^40
        + 3119128829354067839696088095826853682395) * 10^40
        + 7995118752867863739686569299328811966837) * 10^40
        + 1436282785581072123982363164064928424544) * 10^40
        + 7775778229372421296168307884565749885142) * 10^40
        + 1038670213316638986998094076050075433867) * 10^40
        + 4331832556817429882704392841378335426606) * 10^40
        + 4821838399954811277793888108154117033510) * 10^40
        + 6778489066172794345040245646641937684593) * 10^40
        + 54926876678909910542330310100474713536) * 10^40
        + 5426278587480298679747536452840751258675) * 10^40
        + 3162143658597268544654086671311215924351) : ℚ) /
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
    (((-((((((((18975355267711588815 * 10^40
        + 6672328044242858330074453027400412940226) * 10^40
        + 800752205767563320979875438474703883873) * 10^40
        + 5999880495447254964791222304615525619936) * 10^40
        + 2490105109906968580350365929898462260914) * 10^40
        + 3137670833974467082729167218956513531611) * 10^40
        + 9957861405268074749304350533992172092763) * 10^40
        + 3261382884028983980291069231692708157043) * 10^40
        + 3749029235428348507662794063426400357137)) : ℚ) /
        ((((((((120 * 10^40
        + 7731833094884228091258638601579652450792) * 10^40
        + 5699710961462838348432150773393985070522) * 10^40
        + 6399427775360131496252751555462364106065) * 10^40
        + 4234385382175846246308220899352256464295) * 10^40
        + 7630824250931836732072570399987819269924) * 10^40
        + 8802249073488821075147654112046589997727) * 10^40
        + 1328398895320384255511714236208576559245) * 10^40
        + 3043865454385315371752676881473472561152)))

noncomputable def pairedN02701PlusP023Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP023BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP023Center2553‖ ≤ pairedN02701PlusP023Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP023Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP023Input2553]
  have hs : compactExp2547 pairedN02701PlusP023Input2553 16 =
      (pairedN02701PlusP023Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP023Input2553 16).2 : ℝ) =
      pairedN02701PlusP023Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP023Error2553]
  have h := compactExp_error2547 pairedN02701PlusP023Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP023Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP023Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP023DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP023Factor2553 * embedPair2542 pairedN02701PlusP023Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP023Factor2553 : ℝ) * pairedN02701PlusP023Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP023Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP023Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP023BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP023Factor2553)

def pairedN02701PlusP024Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((748320139291177557999687593 : ℚ) /
        236118324143482260684800000000))

def pairedN02701PlusP024Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP024Factor2553 : RatPair2542 := ((((((((((((((75741251671802774309895520797742
    *
    10^40
        + 9865520032259121086144288274324585380029) * 10^40
        + 8196890842192884428122573351254346846032) * 10^40
        + 2498700085977575325006979603128999287734) * 10^40
        + 2911591680012058420283528121485294735181) * 10^40
        + 8658719742023918957594980789732245733255) * 10^40
        + 4783183464333076357235918950905162863144) * 10^40
        + 2790105367868130389823812561574507132793) * 10^40
        + 3339623223825651193945287188550393097294) * 10^40
        + 9725434347570090705910812034965199300397) * 10^40
        + 3023741940787708372064655731934033871299) * 10^40
        + 1075702388560174072538719335360700737471) : ℚ) /
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
    (((-((((((((19548663851129272306 * 10^40
        + 7404256105634666498958730109676877425067) * 10^40
        + 2569771834601588550817308241281634405002) * 10^40
        + 173764695519556901246764406694771257925) * 10^40
        + 5720448399535176193106874943055645854493) * 10^40
        + 1143444239658862060029628748176247677696) * 10^40
        + 3302692291223355501067164932739823972651) * 10^40
        + 4364056512446834181220827722935065183498) * 10^40
        + 9176101831092035674759879782769639782863)) : ℚ) /
        ((((((((120 * 10^40
        + 7731833094884228091258638601579652450792) * 10^40
        + 5699710961462838348432150773393985070522) * 10^40
        + 6399427775360131496252751555462364106065) * 10^40
        + 4234385382175846246308220899352256464295) * 10^40
        + 7630824250931836732072570399987819269924) * 10^40
        + 8802249073488821075147654112046589997727) * 10^40
        + 1328398895320384255511714236208576559245) * 10^40
        + 3043865454385315371752676881473472561152)))

noncomputable def pairedN02701PlusP024Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP024BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP024Center2553‖ ≤ pairedN02701PlusP024Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP024Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP024Input2553]
  have hs : compactExp2547 pairedN02701PlusP024Input2553 16 =
      (pairedN02701PlusP024Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP024Input2553 16).2 : ℝ) =
      pairedN02701PlusP024Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP024Error2553]
  have h := compactExp_error2547 pairedN02701PlusP024Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP024Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP024Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP024DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP024Factor2553 * embedPair2542 pairedN02701PlusP024Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP024Factor2553 : ℝ) * pairedN02701PlusP024Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP024Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP024Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP024BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP024Factor2553)

def pairedN02701PlusP025Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((24244894162688885003625027 : ℚ) /
        7378697629483820646400000000))

def pairedN02701PlusP025Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP025Factor2553 : RatPair2542 := ((((((((((((((73966066085651914686445909015 *
    10^40
        + 9344242818967242253732769151142791644170) * 10^40
        + 3202406391948910157899442070221192615328) * 10^40
        + 8891029212060892637281473451082846631972) * 10^40
        + 302822707479814318184747778787764208492) * 10^40
        + 3655167827355328731241534169912896959778) * 10^40
        + 4617569747006054306840585846298133951852) * 10^40
        + 4310410630270800643490883178654201642001) * 10^40
        + 1216322726812718620680402598075340606490) * 10^40
        + 4856286177440022957492982540634485019701) * 10^40
        + 2102574678085122149207993266950142465412) * 10^40
        + 5089301605164838910424489334799669007687) : ℚ) /
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
    (((-((((((((206171545560330 * 10^40
        + 2566488953333262937537689944486039993007) * 10^40
        + 4474572957465203284547925731527144395904) * 10^40
        + 4156827797969107764988490067116543867286) * 10^40
        + 8370315566233043114860917160826764278312) * 10^40
        + 3979319754024362451907206988338283716251) * 10^40
        + 7090551945134655631035110959921414409803) * 10^40
        + 7199008705048914918657011598910313294408) * 10^40
        + 7355050468067972718097240576700644905407)) : ℚ) /
        (((((((12285683523507529989535101711034949264 * 10^40
        + 258033240874852120344527508044162943370) * 10^40
        + 2649194330116529949254315722163446679322) * 10^40
        + 3680157820489320636456769899708041913416) * 10^40
        + 1813940743247995318977173589786783730257) * 10^40
        + 8727709983816258634654491655010091619771) * 10^40
        + 2984937829578606367841140866233685389979) * 10^40
        + 6472707558852685397495236741911636082688)))

noncomputable def pairedN02701PlusP025Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP025BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP025Center2553‖ ≤ pairedN02701PlusP025Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP025Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP025Input2553]
  have hs : compactExp2547 pairedN02701PlusP025Input2553 16 =
      (pairedN02701PlusP025Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP025Input2553 16).2 : ℝ) =
      pairedN02701PlusP025Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP025Error2553]
  have h := compactExp_error2547 pairedN02701PlusP025Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP025Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP025Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP025DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP025Factor2553 * embedPair2542 pairedN02701PlusP025Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP025Factor2553 : ℝ) * pairedN02701PlusP025Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP025Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP025Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP025BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP025Factor2553)

def pairedN02701PlusP026Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((50247333217324293119390103 : ℚ) /
        14757395258967641292800000000))

def pairedN02701PlusP026Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP026Factor2553 : RatPair2542 := ((((((((((((((295864264342213688173282892168 *
    10^40
        + 3332180680479621926726660245501784175532) * 10^40
        + 3798234661968940429436615879194738456842) * 10^40
        + 4932715771674860965752948835139574551103) * 10^40
        + 8262284458740043977600209532277707188139) * 10^40
        + 6438070869730643930374646243607974380246) * 10^40
        + 7882801196134419752537631626414816983314) * 10^40
        + 5282896818189617160331026163889056795204) * 10^40
        + 3147599696318797417734892095918516019280) * 10^40
        + 5831026152354817151864146299183828277388) * 10^40
        + 6875261701465569480134542366570768150314) * 10^40
        + 2300729818524816064701690120229843076671) : ℚ) /
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
    (((-((((((((1709154971794722 * 10^40
        + 5758804693700058357219927293003326281481) * 10^40
        + 320693828238884649709285096584935751755) * 10^40
        + 731657924015082473245794529639300157443) * 10^40
        + 8130625402165953738855607635035588900272) * 10^40
        + 4629555929878253200605285615614343358581) * 10^40
        + 5596715849759315334754134753713475598116) * 10^40
        + 90884195408216341766328767601914569128) * 10^40
        + 9114496382237552607004290525597901494651)) : ℚ) /
        (((((((98285468188060239916280813688279594112 * 10^40
        + 2064265926998816962756220064353303546962) * 10^40
        + 1193554640932239594034525777307573434578) * 10^40
        + 9441262563914565091654159197664335307329) * 10^40
        + 4511525945983962551817388718294269842062) * 10^40
        + 9821679870530069077235933240080732958170) * 10^40
        + 3879502636628850942729126929869483119837) * 10^40
        + 1781660470821483179961893935293088661504)))

noncomputable def pairedN02701PlusP026Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP026BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP026Center2553‖ ≤ pairedN02701PlusP026Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP026Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP026Input2553]
  have hs : compactExp2547 pairedN02701PlusP026Input2553 16 =
      (pairedN02701PlusP026Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP026Input2553 16).2 : ℝ) =
      pairedN02701PlusP026Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP026Error2553]
  have h := compactExp_error2547 pairedN02701PlusP026Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP026Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP026Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP026DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP026Factor2553 * embedPair2542 pairedN02701PlusP026Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP026Factor2553 : ℝ) * pairedN02701PlusP026Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP026Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP026Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP026BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP026Factor2553)

def pairedN02701PlusP027Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((105567055574838531593598713 : ℚ) /
        29514790517935282585600000000))

def pairedN02701PlusP027Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP027Factor2553 : RatPair2542 := ((((((((((((((1183457057366481812549509866406
    *
    10^40
        + 9526453622952995749126480706195825443665) * 10^40
        + 5311635418237955889823587772676654909855) * 10^40
        + 4789813004631452020420735951188215937996) * 10^40
        + 7073702623458102765283568341276649849754) * 10^40
        + 1966012325132571374939726059546057804298) * 10^40
        + 7560599402205508255547249314184356159516) * 10^40
        + 1569770095689632441670896086038620560558) * 10^40
        + 9007340238374970650935696798925840632679) * 10^40
        + 2909197071853329491674637004806780357887) * 10^40
        + 2957283515907861373075218651511590148273) * 10^40
        + 8324098025426912620045637195658308905247) : ℚ) /
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
    (((-((((((((43090157349377337 * 10^40
        + 6488318792114258490470239509736612497922) * 10^40
        + 1921960564287536240393789516171598050204) * 10^40
        + 4345682745638901102873766260151975470910) * 10^40
        + 6174424030611855007891913619345379718379) * 10^40
        + 8763644534919165322932191575865450516956) * 10^40
        + 3139546887898739151404674056927840075119) * 10^40
        + 3610203830101000242876355086681456878805) * 10^40
        + 400834506584162698375041161104754787679)) : ℚ) /
        (((((((2358851236513445757990739528518710258692 * 10^40
        + 9542382247971607106149281544479285127090) * 10^40
        + 8645311382373750256828618655381762429894) * 10^40
        + 6590301533949562199699820743944047375906) * 10^40
        + 8276622703615101243617329239062476209511) * 10^40
        + 5720316892721657853662397761937590996089) * 10^40
        + 3108063279092422625499046316867594876092) * 10^40
        + 2759851299715596319085454447034127876096)))

noncomputable def pairedN02701PlusP027Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP027BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP027Center2553‖ ≤ pairedN02701PlusP027Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP027Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP027Input2553]
  have hs : compactExp2547 pairedN02701PlusP027Input2553 16 =
      (pairedN02701PlusP027Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP027Input2553 16).2 : ℝ) =
      pairedN02701PlusP027Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP027Error2553]
  have h := compactExp_error2547 pairedN02701PlusP027Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP027Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP027Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP027DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP027Factor2553 * embedPair2542 pairedN02701PlusP027Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP027Factor2553 : ℝ) * pairedN02701PlusP027Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP027Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP027Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP027BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP027Factor2553)

def pairedN02701PlusP028Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((430301136886435135522330613 : ℚ) /
        118059162071741130342400000000))

def pairedN02701PlusP028Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP028Factor2553 : RatPair2542 := ((((((((((((((18935312917848160813477071176526
    *
    10^40
        + 2511749885301878062766171343254469097946) * 10^40
        + 8578656168700382063754304972742098859203) * 10^40
        + 81225179279339885992304547575967002672) * 10^40
        + 5571377889278055686415578473570638737940) * 10^40
        + 1381961705345361753124009726752408534868) * 10^40
        + 2268166077255261727112292867345860517815) * 10^40
        + 3818877969205600990807913471248695572273) * 10^40
        + 7436395196237007098533785147750231325215) * 10^40
        + 2891867443212586233173925413195781193639) * 10^40
        + 3782470002012843425753834477334767547897) * 10^40
        + 4699816886143271866920936525731732122967) : ℚ) /
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
    (((-((((((((255475620358834787 * 10^40
        + 4835709776847294837191301718350450847737) * 10^40
        + 5533763829077120755651577532965693134403) * 10^40
        + 1630598740068020647828169880479058874632) * 10^40
        + 1619225506587630654070413361052392905114) * 10^40
        + 2518826128145652959878156224279646948249) * 10^40
        + 902642794337933566336040415108202803885) * 10^40
        + 1707787003817935291487035656398647655970) * 10^40
        + 4216704970527140836775676363645023239409)) : ℚ) /
        ((((((((1 * 10^40
        + 3724225376078229864673393620472496050577) * 10^40
        + 1882951260925714072141274440606749830346) * 10^40
        + 8481811679265456039730144904039345046659) * 10^40
        + 8343572561161089161889866146583548368912) * 10^40
        + 4518532093760589053773551936363497946249) * 10^40
        + 1463661921289645694035768796727802159065) * 10^40
        + 810549987446822548358087661775097460900) * 10^40
        + 5148225743799833129224462237289471279104)))

noncomputable def pairedN02701PlusP028Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP028BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP028Center2553‖ ≤ pairedN02701PlusP028Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP028Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP028Input2553]
  have hs : compactExp2547 pairedN02701PlusP028Input2553 16 =
      (pairedN02701PlusP028Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP028Input2553 16).2 : ℝ) =
      pairedN02701PlusP028Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP028Error2553]
  have h := compactExp_error2547 pairedN02701PlusP028Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP028Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP028Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP028DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP028Factor2553 * embedPair2542 pairedN02701PlusP028Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP028Factor2553 : ℝ) * pairedN02701PlusP028Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP028Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP028Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP028BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP028Factor2553)

def pairedN02701PlusP029Input2553 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((442530733595656525480647121 : ℚ) /
        118059162071741130342400000000))

def pairedN02701PlusP029Center2553 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def pairedN02701PlusP029Factor2553 : RatPair2542 := ((((((((((((((18935312917823927119129905790077
    *
    10^40
        + 8558973257615288732110989851657602011738) * 10^40
        + 3959171259047486090331321400920240956950) * 10^40
        + 1276243310550908822985659277998461419390) * 10^40
        + 9660544657589982087394547144103789296408) * 10^40
        + 7508829199027421948296773067070882078169) * 10^40
        + 2841885958348292525927254006046831583752) * 10^40
        + 1788448244254718018864643229167641021423) * 10^40
        + 3292662256996355657382347648729248441247) * 10^40
        + 4621819942626154426543549297918407837539) * 10^40
        + 7854315182220819080450586474233395496532) * 10^40
        + 5073927329364057448896152697772724579759) : ℚ) /
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
    (((-((((((((2890101475500502288 * 10^40
        + 5020492026924458515869650902584294355071) * 10^40
        + 6134670667335966484280833910619647853713) * 10^40
        + 37394811493219587091884986471980059047) * 10^40
        + 7103980594724246332600831435033036611130) * 10^40
        + 5200521563820077804032455513767089895774) * 10^40
        + 2745377768489474249741353865220129989708) * 10^40
        + 849244353888637682374253603023883876126) * 10^40
        + 2038377869078698283821068006687062426839)) : ℚ) /
        ((((((((15 * 10^40
        + 966479136860528511407329825197456556349) * 10^40
        + 712463870182854793554018846674248133815) * 10^40
        + 3299928471920016437031593944432795513258) * 10^40
        + 1779298172771980780788527612419032058036) * 10^40
        + 9703853031366479591509071299998477408740) * 10^40
        + 6100281134186102634393456764005823749715) * 10^40
        + 8916049861915048031938964279526072069905) * 10^40
        + 6630483181798164421469084610184184070144)))

noncomputable def pairedN02701PlusP029Error2553 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem pairedN02701PlusP029BaseError2553 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP029Center2553‖ ≤ pairedN02701PlusP029Error2553 := by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hz : ‖embedPair2542 pairedN02701PlusP029Input2553‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, pairedN02701PlusP029Input2553]
  have hs : compactExp2547 pairedN02701PlusP029Input2553 16 =
      (pairedN02701PlusP029Center2553, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 pairedN02701PlusP029Input2553 16).2 : ℝ) =
      pairedN02701PlusP029Error2553
      := by
    rw [hs]
    norm_num [pairedN02701PlusP029Error2553]
  have h := compactExp_error2547 pairedN02701PlusP029Input2553 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      pairedN02701PlusPosition2553 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          pairedN02701PlusP029Input2553) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [pairedN02701PlusPosition2553, storedWidth, nodeModulation2541,
      embedPair2542, pairedN02701PlusP029Input2553, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem pairedN02701PlusP029DerivativeError2553 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ pairedN02701PlusPosition2553 -
      embedPair2542 pairedN02701PlusP029Factor2553 * embedPair2542 pairedN02701PlusP029Center2553‖
          ≤
        (pairMagnitude2542 pairedN02701PlusP029Factor2553 : ℝ) * pairedN02701PlusP029Error2553 :=
            by
  have hx : |pairedN02701PlusPosition2553| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [pairedN02701PlusPosition2553, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) pairedN02701PlusPosition2553 = embedPair2542
          pairedN02701PlusP029Factor2553 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      pairedN02701PlusPosition2553, storedWidth, nodeModulation2541, embedPair2542,
      pairedN02701PlusP029Factor2553, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ pairedN02701PlusP029BaseError2553
    (embedPair_magnitude2542 pairedN02701PlusP029Factor2553)

theorem pairedN02701PlusGrid2553 :
    -stripRadius2303 + (2701 : ℝ) * (2 * stripRadius2303 / 10240) =
      pairedN02701PlusPosition2553 := by
  norm_num [stripRadius2303, pairedN02701PlusPosition2553]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.pairedN02701PlusP000DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP001DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP002DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP003DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP004DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP005DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP006DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP007DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP008DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP009DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP010DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP011DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP012DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP013DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP014DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP015DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP016DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP017DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP018DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP019DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP020DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP021DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP022DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP023DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP024DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP025DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP026DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP027DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP028DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusP029DerivativeError2553
#print axioms ConnesWeilRH.Dev.pairedN02701PlusGrid2553
