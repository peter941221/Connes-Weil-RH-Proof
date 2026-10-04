import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def corrSecondN02701PlusPointPosition2575 : ℝ := (((-158531586419) : ℝ) /
        51200000000)

theorem corrSecondN02701PlusPointZero2575 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def corrSecondN02701PlusPointP000Center2575 : RatPair2542 := (0, 0)

def corrSecondN02701PlusPointP000Factor2575 : RatPair2542 := (0, 0)

noncomputable def corrSecondN02701PlusPointP000Error2575 : ℝ := 0

theorem corrSecondN02701PlusPointP000Exterior2575 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02701PlusPointPosition2575 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |corrSecondN02701PlusPointPosition2575| := by
    norm_num [storedWidth, corrSecondN02701PlusPointPosition2575]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem corrSecondN02701PlusPointP000BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP000Center2575‖ ≤
          corrSecondN02701PlusPointP000Error2575 := by
  rw [corrSecondN02701PlusPointP000Exterior2575]
  norm_num [corrSecondN02701PlusPointP000Center2575, corrSecondN02701PlusPointP000Error2575,
      corrSecondN02701PlusPointZero2575]

theorem corrSecondN02701PlusPointP000DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP000Factor2575 * embedPair2542
          corrSecondN02701PlusPointP000Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP000Factor2575 : ℝ) *
            corrSecondN02701PlusPointP000Error2575 := by
  rw [corrSecondN02701PlusPointP000Exterior2575]
  norm_num [corrSecondN02701PlusPointP000Factor2575, corrSecondN02701PlusPointP000Center2575,
      corrSecondN02701PlusPointP000Error2575,
      corrSecondN02701PlusPointZero2575, pairMagnitude2542]

def corrSecondN02701PlusPointP001Input2575 : RatPair2542 := ((((-((340 * 10^40
        + 1125558694715412604882605546165965236561) * 10^40
        + 9325600687173468560131001925406640200979)) : ℚ) /
        ((941 * 10^40
        + 6102169216506454849034257242358098754684) * 10^40
        + 4000368461807982441421667880140800000000)),
    ((875774620147323865939848151 : ℚ) /
        3689348814741910323200000000))

def corrSecondN02701PlusPointP001Center2575 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP001Factor2575 : RatPair2542 :=
    ((((((((((7453421272567857588726740829653 * 10^40
        + 3014204827775927440626099043706658128718) * 10^40
        + 8835574580480310140598470099933449621097) * 10^40
        + 759642697134895511562420923691020303777) * 10^40
        + 6220255984722906798753615527717623072188) * 10^40
        + 9804669574979278020558656723224692097640) * 10^40
        + 2737401822211164766397176963473158917917) * 10^40
        + 967509209465423997451429330051967632855) : ℚ) /
        (((((((20607464985904378613958700 * 10^40
        + 2595159148890025498073864656791828969138) * 10^40
        + 3290271723839544840116734095165196842913) * 10^40
        + 467218176066478541785588708334274916834) * 10^40
        + 5928978601939523898086459863702066739961) * 10^40
        + 1122900486430430706333686109357355611694) * 10^40
        + 7954245854741826417223689275212605633229) * 10^40
        + 4940715927363866938280641064052010778624)),
    (((-(((21601892067313936388898922846091120295 * 10^40
        + 5959773697588567228599056982451915850242) * 10^40
        + 1473794743465736676054620176731954915661) * 10^40
        + 7623433035753004811318258345182493030349)) : ℚ) /
        (((453954457912953847599410478691028 * 10^40
        + 1779924909704564993115249489169742548465) * 10^40
        + 2128249869612705703746351004084215377754) * 10^40
        + 876988830001680477006235447041424621568)))

noncomputable def corrSecondN02701PlusPointP001Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP001BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP001Center2575‖ ≤
          corrSecondN02701PlusPointP001Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP001Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP001Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP001Input2575 9 =
      (corrSecondN02701PlusPointP001Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP001Input2575 9).2 : ℝ) =
      corrSecondN02701PlusPointP001Error2575 := by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP001Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP001Input2575 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          corrSecondN02701PlusPointP001Input2575)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP001Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP001DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP001Factor2575 * embedPair2542
          corrSecondN02701PlusPointP001Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP001Factor2575 : ℝ) *
            corrSecondN02701PlusPointP001Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP001Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP001Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP001BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP001Factor2575)

def corrSecondN02701PlusPointP002Input2575 : RatPair2542 := ((((-((9033 * 10^40
        + 8109252320354666245907324545684805984286) * 10^40
        + 2898018879638657721153554737628069387539)) : ℚ) /
        ((36680 * 10^40
        + 5267114824128922047222362789138794665314) * 10^40
        + 902751818529719531373343041126400000000)),
    (((-875774620147323865939848151) : ℚ) /
        1844674407370955161600000000))

def corrSecondN02701PlusPointP002Center2575 : RatPair2542 := ((((-168036782698919993429) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-252698714645137902289) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def corrSecondN02701PlusPointP002Factor2575 : RatPair2542 :=
    ((((((((((129851041645849122828200179206278339 *
    10^40
        + 4913823320069702644701008154495144108710) * 10^40
        + 9825260252125856490011474756898456541402) * 10^40
        + 8189051949334347208129849089764492697764) * 10^40
        + 6751216722387036822588742417369664706106) * 10^40
        + 2844874286279062415096900940720697335578) * 10^40
        + 5052099598088772797393885069829066357973) * 10^40
        + 9986351765395634463428995363479058269655) : ℚ) /
        (((((((759280344898816204453149405320788 * 10^40
        + 2562755322010977854069761205418464326627) * 10^40
        + 5898745153495915958343318913963452743824) * 10^40
        + 3252926811272942913028468180398675049644) * 10^40
        + 9236371670745830152415062103830109362394) * 10^40
        + 2100223503579552350555864490642376213996) * 10^40
        + 8684472799811869662047026269274168847585) * 10^40
        + 5890140663961686575747173712578387902464)),
    (((((9131252987573640161554318505062946191665 * 10^40
        + 3997827606651248825545918416739806177012) * 10^40
        + 1815185446315106026552274082359101358309) * 10^40
        + 7305615912570677022691238790576858347469) : ℚ) /
        (((2755504209575474781138380549191462978 * 10^40
        + 6825593386581207281056339534128529847042) * 10^40
        + 7275016703069080889991558353505182267414) * 10^40
        + 7315590532715512968354674442604703121408)))

noncomputable def corrSecondN02701PlusPointP002Error2575 : ℝ := ((2260016183526325913 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP002BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP002Center2575‖ ≤
          corrSecondN02701PlusPointP002Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP002Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP002Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP002Input2575 8 =
      (corrSecondN02701PlusPointP002Center2575, ((2260016183526325913 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP002Input2575 8).2 : ℝ) =
      corrSecondN02701PlusPointP002Error2575 := by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP002Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP002Input2575 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          corrSecondN02701PlusPointP002Input2575)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP002Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP002DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP002Factor2575 * embedPair2542
          corrSecondN02701PlusPointP002Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP002Factor2575 : ℝ) *
            corrSecondN02701PlusPointP002Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP002Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP002Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP002BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP002Factor2575)

def corrSecondN02701PlusPointP003Input2575 : RatPair2542 := ((((-((1204018 * 10^40
        + 3199206753711006565389390034201102437777) * 10^40
        + 7349271424128768512973515705970498543953)) : ℚ) /
        ((6644764 * 10^40
        + 348595898346936727630550565694213304645) * 10^40
        + 356964576015918677191939509452800000000)),
    (((-875774620147323865939848151) : ℚ) /
        1844674407370955161600000000))

def corrSecondN02701PlusPointP003Center2575 : RatPair2542 := ((((-5788973884569169910793434755) :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-4352815604563173678616329029) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def corrSecondN02701PlusPointP003Factor2575 : RatPair2542 := ((((-((((((((982241 * 10^40
        + 9456437335421627033374095646608247471404) * 10^40
        + 685198574720813389897169163916260597954) * 10^40
        + 2960514024101374676342670661710807088176) * 10^40
        + 323068404307734474945898111210705203703) * 10^40
        + 176750763304130746231167933843597413986) * 10^40
        + 300572997123449907262284725100632345293) * 10^40
        + 2406958904200217229105627821411371371302) * 10^40
        + 1605493143266800264942566357875711590305)) : ℚ) /
        ((((((((735 * 10^40
        + 9031578952271773711277727944517603986909) * 10^40
        + 4299908468254782876318386098252753667384) * 10^40
        + 8035978194544546520050508311085649632775) * 10^40
        + 400074100802200631812660752661470157903) * 10^40
        + 5226728248472081247871991151670895911425) * 10^40
        + 8584895352049947641835514097188246337603) * 10^40
        + 3382474669940090816110002118475276189617) * 10^40
        + 8499698954555383858007879986387213090816)),
    ((((((31572 * 10^40
        + 7489131687043148243314382146315325505982) * 10^40
        + 4842829986362381075375783704996807820019) * 10^40
        + 7525069411294730109524483233340942916616) * 10^40
        + 1158757319259109502989549661100142435503) : ℚ) /
        ((((27 * 10^40
        + 1275350501151721831636617526493081859830) * 10^40
        + 371775513702883693023963091771403332187) * 10^40
        + 5225040598366931331057220453837234929427) * 10^40
        + 5352048433052554802286703513941254864896)))

noncomputable def corrSecondN02701PlusPointP003Error2575 : ℝ := ((36476409710489096549727441 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP003BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP003Center2575‖ ≤
          corrSecondN02701PlusPointP003Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP003Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP003Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP003Input2575 8 =
      (corrSecondN02701PlusPointP003Center2575, ((36476409710489096549727441 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP003Input2575 8).2 : ℝ) =
      corrSecondN02701PlusPointP003Error2575 := by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP003Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP003Input2575 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          corrSecondN02701PlusPointP003Input2575)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP003Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP003DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP003Factor2575 * embedPair2542
          corrSecondN02701PlusPointP003Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP003Factor2575 : ℝ) *
            corrSecondN02701PlusPointP003Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP003Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP003Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP003BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP003Factor2575)

def corrSecondN02701PlusPointP004Input2575 : RatPair2542 := ((((-((21030 * 10^40
        + 4978280417753696551825490501735319367009) * 10^40
        + 9100087780138783714176925758135881887539)) : ℚ) /
        ((134028 * 10^40
        + 5763226050861645114137505055527745988340) * 10^40
        + 4359916327702839531373343041126400000000)),
    ((875774620147323865939848151 : ℚ) /
        1844674407370955161600000000))

def corrSecondN02701PlusPointP004Center2575 : RatPair2542 := ((((-725790656500916187131713370187)
    : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((4365862355930743774088204387843 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def corrSecondN02701PlusPointP004Factor2575 : RatPair2542 :=
    ((((-(((((((201250877587865433832594056688601115025 *
    10^40
        + 178924490793867483545640069847408792599) * 10^40
        + 8745933739430013072055088891363552035795) * 10^40
        + 7335793678025502556086171736515649999904) * 10^40
        + 3959496082423144904199853211201800605374) * 10^40
        + 6875442655459253724339838660175784987705) * 10^40
        + 7052082236553568560865928644773833060254) * 10^40
        + 8683417772681280585223869382614691730345)) : ℚ) /
        (((((((135347276887106627857315383444605739 * 10^40
        + 9991691964880965341918750282532925631821) * 10^40
        + 7593644714309317200092186362824769527439) * 10^40
        + 6382506515583507680681236206264303987138) * 10^40
        + 2902368533592603132790791778952058210570) * 10^40
        + 6226284060945507959518899118947584203178) * 10^40
        + 9302318401510404933239847161850597735717) * 10^40
        + 4009126728727183218511973712578387902464)),
    (((-((((2 * 10^40
        + 2148447075076592916634499147755891243627) * 10^40
        + 7085096436311738008115224457846337982816) * 10^40
        + 1835355949640455546385709166261242335362) * 10^40
        + 8940649471812326579198136593311233347469)) : ℚ) /
        (((36789574187139843526753432905043948801 * 10^40
        + 9159438194521168849766900670326046515891) * 10^40
        + 7851531537127144730886893054125014016304) * 10^40
        + 366335614660560978287474442604703121408)))

noncomputable def corrSecondN02701PlusPointP004Error2575 : ℝ := ((17853934217737043702764082891 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP004BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP004Center2575‖ ≤
          corrSecondN02701PlusPointP004Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP004Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP004Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP004Input2575 8 =
      (corrSecondN02701PlusPointP004Center2575, ((17853934217737043702764082891 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP004Input2575 8).2 : ℝ) =
      corrSecondN02701PlusPointP004Error2575 := by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP004Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP004Input2575 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          corrSecondN02701PlusPointP004Input2575)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP004Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP004DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP004Factor2575 * embedPair2542
          corrSecondN02701PlusPointP004Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP004Factor2575 : ℝ) *
            corrSecondN02701PlusPointP004Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP004Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP004Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP004BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP004Factor2575)

def corrSecondN02701PlusPointP005Center2575 : RatPair2542 := (0, 0)

def corrSecondN02701PlusPointP005Factor2575 : RatPair2542 := (0, 0)

noncomputable def corrSecondN02701PlusPointP005Error2575 : ℝ := 0

theorem corrSecondN02701PlusPointP005Exterior2575 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02701PlusPointPosition2575 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |corrSecondN02701PlusPointPosition2575| := by
    norm_num [storedWidth, corrSecondN02701PlusPointPosition2575]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem corrSecondN02701PlusPointP005BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP005Center2575‖ ≤
          corrSecondN02701PlusPointP005Error2575 := by
  rw [corrSecondN02701PlusPointP005Exterior2575]
  norm_num [corrSecondN02701PlusPointP005Center2575, corrSecondN02701PlusPointP005Error2575,
      corrSecondN02701PlusPointZero2575]

theorem corrSecondN02701PlusPointP005DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP005Factor2575 * embedPair2542
          corrSecondN02701PlusPointP005Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP005Factor2575 : ℝ) *
            corrSecondN02701PlusPointP005Error2575 := by
  rw [corrSecondN02701PlusPointP005Exterior2575]
  norm_num [corrSecondN02701PlusPointP005Factor2575, corrSecondN02701PlusPointP005Center2575,
      corrSecondN02701PlusPointP005Error2575,
      corrSecondN02701PlusPointZero2575, pairMagnitude2542]

def corrSecondN02701PlusPointP006Input2575 : RatPair2542 :=
    ((((-43838019295084218252511359948400647) : ℚ) /
        73447401531966028759865753600000000),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP006Center2575 : RatPair2542 := (((483449294895075 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP006Factor2575 : RatPair2542 := (((((1822342085289 * 10^40
        + 5214561788358910248038060114372879425593) * 10^40
        + 8414582624139595755545470189049347426649) : ℚ) /
        ((354951109 * 10^40
        + 6805509743719437539166977228721393891763) * 10^40
        + 5385343191475503022181880756197389706596)),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP006Error2575 : ℝ := ((2446198475405 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP006BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP006Center2575‖ ≤
          corrSecondN02701PlusPointP006Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP006Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP006Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP006Input2575 7 =
      (corrSecondN02701PlusPointP006Center2575, ((2446198475405 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP006Input2575 7).2 : ℝ) =
      corrSecondN02701PlusPointP006Error2575 := by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP006Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP006Input2575 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          corrSecondN02701PlusPointP006Input2575)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP006Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP006DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP006Factor2575 * embedPair2542
          corrSecondN02701PlusPointP006Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP006Factor2575 : ℝ) *
            corrSecondN02701PlusPointP006Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP006Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP006Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP006BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP006Factor2575)

def corrSecondN02701PlusPointP007Input2575 : RatPair2542 := ((((-((1204018 * 10^40
        + 3199206753711006565389390034201102437777) * 10^40
        + 7349271424128768512973515705970498543953)) : ℚ) /
        ((1661191 * 10^40
        + 87148974586734181907637641423553326161) * 10^40
        + 2589241144003979669297984877363200000000)),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP007Center2575 : RatPair2542 := (((163354299886446954699714643 : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP007Factor2575 : RatPair2542 := ((((((((((306162482638448552 * 10^40
        + 998866454356609504309305246529531883844) * 10^40
        + 531911194803083682964308937834531142524) * 10^40
        + 2785342351756243334470672512127596100080) * 10^40
        + 9341623736905870613687070897829289084460) * 10^40
        + 1831168146672864438702104923638525421711) * 10^40
        + 1295343600746890817289974894212301504416) * 10^40
        + 3718890182701606409141049106826999073849) : ℚ) /
        (((((((1486144592108109 * 10^40
        + 351518717093385914474283486670956107430) * 10^40
        + 3716008898762888692893937658899926663252) * 10^40
        + 3233287319177341251268176652695887279274) * 10^40
        + 381335793586902065623676943706627828617) * 10^40
        + 8404143079017247388996586247213416310279) * 10^40
        + 3936525874344426134969636744699691464032) * 10^40
        + 4213672730806425636564196427307996295396)),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP007Error2575 : ℝ := ((759335337735088749674751 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem corrSecondN02701PlusPointP007BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP007Center2575‖ ≤
          corrSecondN02701PlusPointP007Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP007Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP007Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP007Input2575 6 =
      (corrSecondN02701PlusPointP007Center2575, ((759335337735088749674751 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP007Input2575 6).2 : ℝ) =
      corrSecondN02701PlusPointP007Error2575 := by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP007Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP007Input2575 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          corrSecondN02701PlusPointP007Input2575)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP007Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP007DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP007Factor2575 * embedPair2542
          corrSecondN02701PlusPointP007Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP007Factor2575 : ℝ) *
            corrSecondN02701PlusPointP007Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP007Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP007Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP007BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP007Factor2575)

def corrSecondN02701PlusPointP008Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((630729240492097551551105443 : ℚ) /
        944473296573929042739200000000))

def corrSecondN02701PlusPointP008Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP008Factor2575 : RatPair2542 := (((((((((((66262 * 10^40
        + 1363232436104974126807194883895168372061) * 10^40
        + 8987413504679658328920470685478344996902) * 10^40
        + 6383331117858436334053145738804023815105) * 10^40
        + 780004089341989888440738129945009280853) * 10^40
        + 9536892404915062860712590984728875882254) * 10^40
        + 269650133515263863941979799986577134908) * 10^40
        + 9655986384802886240469826044984914336866) * 10^40
        + 5244195841727679033149710370851493158375) : ℚ) /
        (((((((823819277521727754964053000504 * 10^40
        + 6318722980635607003224410735821333321910) * 10^40
        + 1018483369370914779966842705673288550011) * 10^40
        + 9635008373271080735354764223925241063329) * 10^40
        + 4077273132841785916924162736494558364756) * 10^40
        + 8044984404365642773705182313102669232270) * 10^40
        + 3046943372968140737767944563703744084411) * 10^40
        + 6248921813475847465352479945548852363264)),
    (((-((((7277 * 10^40
        + 1620192937614224973524990561676007599720) * 10^40
        + 7105936771672490481777816517737291331558) * 10^40
        + 9167270352710386045609796564756031836286) * 10^40
        + 7320176170546645714693654783002818953979)) : ℚ) /
        (((90764490717555825162209184345262136 * 10^40
        + 6890592425225252898486011682894882747208) * 10^40
        + 8547055885218282812081156336193500973985) * 10^40
        + 3216446206340766659354847027882509729792)))

noncomputable def corrSecondN02701PlusPointP008Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP008BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP008Center2575‖ ≤
          corrSecondN02701PlusPointP008Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP008Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP008Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP008Input2575 16 =
      (corrSecondN02701PlusPointP008Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP008Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP008Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP008Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP008Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP008Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP008Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP008DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP008Factor2575 * embedPair2542
          corrSecondN02701PlusPointP008Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP008Factor2575 : ℝ) *
            corrSecondN02701PlusPointP008Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP008Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP008Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP008BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP008Factor2575)

def corrSecondN02701PlusPointP009Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((938059634128117561826070909 : ℚ) /
        944473296573929042739200000000))

def corrSecondN02701PlusPointP009Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP009Factor2575 : RatPair2542 := (((((((((((66262 * 10^40
        + 1363232236628920198662592790117938804971) * 10^40
        + 3821115775654430567025046328664131899264) * 10^40
        + 6644051668362364077901106276252497492522) * 10^40
        + 3075943490915931915637898146331347159368) * 10^40
        + 4119933681004852027328367803790643695271) * 10^40
        + 231476409796028207002291292215825748234) * 10^40
        + 4392876323575678636410524851028820903000) * 10^40
        + 2467351661288612310928917685634407096487) : ℚ) /
        (((((((823819277521727754964053000504 * 10^40
        + 6318722980635607003224410735821333321910) * 10^40
        + 1018483369370914779966842705673288550011) * 10^40
        + 9635008373271080735354764223925241063329) * 10^40
        + 4077273132841785916924162736494558364756) * 10^40
        + 8044984404365642773705182313102669232270) * 10^40
        + 3046943372968140737767944563703744084411) * 10^40
        + 6248921813475847465352479945548852363264)),
    (((-((((3607 * 10^40
        + 6821891560232286158986990683079538528255) * 10^40
        + 4377830537486770444195082344608195487300) * 10^40
        + 9047125921516571628436436378427719851861) * 10^40
        + 8172356009234127842847095223237824261559)) : ℚ) /
        (((30254830239185275054069728115087378 * 10^40
        + 8963530808408417632828670560964960915736) * 10^40
        + 2849018628406094270693718778731166991328) * 10^40
        + 4405482068780255553118282342627503243264)))

noncomputable def corrSecondN02701PlusPointP009Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP009BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP009Center2575‖ ≤
          corrSecondN02701PlusPointP009Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP009Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP009Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP009Input2575 16 =
      (corrSecondN02701PlusPointP009Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP009Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP009Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP009Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP009Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP009Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP009Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP009DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP009Factor2575 * embedPair2542
          corrSecondN02701PlusPointP009Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP009Factor2575 : ℝ) *
            corrSecondN02701PlusPointP009Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP009Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP009Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP009BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP009Factor2575)

def corrSecondN02701PlusPointP010Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((558025679572758329216722299 : ℚ) /
        472236648286964521369600000000))

def corrSecondN02701PlusPointP010Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP010Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5340808021340455630574327990150785245859) * 10^40
        + 3023977753066280929319619802233801439760) * 10^40
        + 8140775699733493601612586423852740398345) * 10^40
        + 1392572897152068964788320408912414883697) * 10^40
        + 5884845032284354962393045419797877050532) * 10^40
        + 1555164960329763090193669047375449436849) * 10^40
        + 468167800970581646499939937436201664782) * 10^40
        + 3578878773787994423628338684038330790295) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((2146 * 10^40
        + 1101533885764898308912780510675451085367) * 10^40
        + 7026400976525613868187053348096950183468) * 10^40
        + 6922435569678653193368210101171971057283) * 10^40
        + 3522549834536611256469177520900202374449)) : ℚ) /
        (((15127415119592637527034864057543689 * 10^40
        + 4481765404204208816414335280482480457868) * 10^40
        + 1424509314203047135346859389365583495664) * 10^40
        + 2202741034390127776559141171313751621632)))

noncomputable def corrSecondN02701PlusPointP010Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP010BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP010Center2575‖ ≤
          corrSecondN02701PlusPointP010Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP010Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP010Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP010Input2575 16 =
      (corrSecondN02701PlusPointP010Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP010Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP010Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP010Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP010Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP010Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP010Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP010DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP010Factor2575 * embedPair2542
          corrSecondN02701PlusPointP010Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP010Factor2575 : ℝ) *
            corrSecondN02701PlusPointP010Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP010Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP010Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP010BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP010Factor2575)

def corrSecondN02701PlusPointP011Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((617361885721254929729880619 : ℚ) /
        472236648286964521369600000000))

def corrSecondN02701PlusPointP011Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP011Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5340807992485419523330155193294602692970) * 10^40
        + 5811741348822640803023616425442704624575) * 10^40
        + 6719552648490030575411690622108333846864) * 10^40
        + 5345526697496492251236792035721073717029) * 10^40
        + 3677349140590491123942655340674220533715) * 10^40
        + 826775064174478687846316946216952775406) * 10^40
        + 7237662896714492140713527358120113113830) * 10^40
        + 2554045052911326047626541260301427502455) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((7122 * 10^40
        + 9335481975018986953996191038510871405191) * 10^40
        + 6208659604548186221353605688115327789664) * 10^40
        + 2520114316357458386618078237158960846563) * 10^40
        + 3230567208275933582509229640933434234307)) : ℚ) /
        (((45382245358777912581104592172631068 * 10^40
        + 3445296212612626449243005841447441373604) * 10^40
        + 4273527942609141406040578168096750486992) * 10^40
        + 6608223103170383329677423513941254864896)))

noncomputable def corrSecondN02701PlusPointP011Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP011BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP011Center2575‖ ≤
          corrSecondN02701PlusPointP011Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP011Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP011Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP011Input2575 16 =
      (corrSecondN02701PlusPointP011Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP011Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP011Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP011Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP011Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP011Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP011Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP011DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP011Factor2575 * embedPair2542
          corrSecondN02701PlusPointP011Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP011Factor2575 : ℝ) *
            corrSecondN02701PlusPointP011Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP011Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP011Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP011BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP011Factor2575)

def corrSecondN02701PlusPointP012Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((13576393469632358173878271 : ℚ) /
        9444732965739290427392000000))

def corrSecondN02701PlusPointP012Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP012Factor2575 : RatPair2542 := (((((((((((4141 * 10^40
        + 3835201989881804268954574027874864674296) * 10^40
        + 7750035691666793421674914555546787208009) * 10^40
        + 279574281238476509629714607455519339891) * 10^40
        + 5233826445101972203741005993408340035480) * 10^40
        + 5553783321399345129872651691410110866123) * 10^40
        + 8463590344220484214865514589050304192606) * 10^40
        + 4554206635871805450507826117616164911919) * 10^40
        + 9740857230092240163857354408111219087551) : ℚ) /
        (((((((51488704845107984685253312531 * 10^40
        + 5394920186289725437701525670988833332619) * 10^40
        + 3813655210585682173747927669104580534375) * 10^40
        + 7477188023329442545959672763995327566458) * 10^40
        + 879829570802611619807760171030909897797) * 10^40
        + 3002811525272852673356573894568916827016) * 10^40
        + 8940433960810508796110496535231484005275) * 10^40
        + 7265557613342240466584529996596803272704)),
    (((-((((3916 * 10^40
        + 73995901213223681256736387915348293170) * 10^40
        + 7961061951715057179493057181324924865550) * 10^40
        + 1305431588358643402686955338550602989613) * 10^40
        + 963652238955893471489052954688963796575)) : ℚ) /
        (((22691122679388956290552296086315534 * 10^40
        + 1722648106306313224621502920723720686802) * 10^40
        + 2136763971304570703020289084048375243496) * 10^40
        + 3304111551585191664838711756970627432448)))

noncomputable def corrSecondN02701PlusPointP012Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP012BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP012Center2575‖ ≤
          corrSecondN02701PlusPointP012Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP012Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP012Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP012Input2575 16 =
      (corrSecondN02701PlusPointP012Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP012Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP012Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP012Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP012Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP012Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP012Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP012DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP012Factor2575 * embedPair2542
          corrSecondN02701PlusPointP012Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP012Factor2575 : ℝ) *
            corrSecondN02701PlusPointP012Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP012Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP012Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP012BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP012Factor2575)

def corrSecondN02701PlusPointP013Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((146965053600227290725850929 : ℚ) /
        94447329657392904273920000000))

def corrSecondN02701PlusPointP013Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP013Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5340807926771092766304614466040957569710) * 10^40
        + 797737927819316419919449215798208407815) * 10^40
        + 9400283785706006195271267964540108722207) * 10^40
        + 2519817528133584051718589337715404136037) * 10^40
        + 9697322495690018501780302655168172611874) * 10^40
        + 9288604728663661508590935457317070072473) * 10^40
        + 1435403111239331746613743103425058540895) * 10^40
        + 2992952269555110715092898167635043943479) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((2826 * 10^40
        + 634346274760070197016663658964935466436) * 10^40
        + 3162019374583779472984005573731135491868) * 10^40
        + 1498189586204931290629920729192606133282) * 10^40
        + 3486023779184461575017868441799775492895)) : ℚ) /
        (((15127415119592637527034864057543689 * 10^40
        + 4481765404204208816414335280482480457868) * 10^40
        + 1424509314203047135346859389365583495664) * 10^40
        + 2202741034390127776559141171313751621632)))

noncomputable def corrSecondN02701PlusPointP013Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP013BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP013Center2575‖ ≤
          corrSecondN02701PlusPointP013Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP013Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP013Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP013Input2575 16 =
      (corrSecondN02701PlusPointP013Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP013Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP013Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP013Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP013Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP013Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP013Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP013DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP013Factor2575 * embedPair2542
          corrSecondN02701PlusPointP013Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP013Factor2575 : ℝ) *
            corrSecondN02701PlusPointP013Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP013Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP013Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP013BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP013Factor2575)

def corrSecondN02701PlusPointP014Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((838597898629083505249081609 : ℚ) /
        472236648286964521369600000000))

def corrSecondN02701PlusPointP014Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP014Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5340807859217395722226792449129056002966) * 10^40
        + 2047799633422379256681670742697983031370) * 10^40
        + 5832198843413717785620559342981261618285) * 10^40
        + 4839910443144955624928874813852903264185) * 10^40
        + 9499049521337479352319507582620740570246) * 10^40
        + 7872460795434391595117895570914803425397) * 10^40
        + 8551950675105937774353024014297340083853) * 10^40
        + 8437969455291911623112682698451291914975) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((9675 * 10^40
        + 4873336803645535994701219322494489459275) * 10^40
        + 3988632377284474423619490141709235098197) * 10^40
        + 8509912900063193309003690552220770811281) * 10^40
        + 3342683423704572824071418938217573301777)) : ℚ) /
        (((45382245358777912581104592172631068 * 10^40
        + 3445296212612626449243005841447441373604) * 10^40
        + 4273527942609141406040578168096750486992) * 10^40
        + 6608223103170383329677423513941254864896)))

noncomputable def corrSecondN02701PlusPointP014Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP014BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP014Center2575‖ ≤
          corrSecondN02701PlusPointP014Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP014Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP014Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP014Input2575 16 =
      (corrSecondN02701PlusPointP014Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP014Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP014Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP014Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP014Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP014Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP014Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP014DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP014Factor2575 * embedPair2542
          corrSecondN02701PlusPointP014Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP014Factor2575 : ℝ) *
            corrSecondN02701PlusPointP014Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP014Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP014Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP014BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP014Factor2575)

def corrSecondN02701PlusPointP015Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((912951341665564226630614693 : ℚ) /
        472236648286964521369600000000))

def corrSecondN02701PlusPointP015Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP015Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5340807805335335847355811703219639047377) * 10^40
        + 1706926656301660220888664231031033986582) * 10^40
        + 8481860043525855230382038492740826429980) * 10^40
        + 2998195204940844771704364151652017591013) * 10^40
        + 8362144900775999628007754619934254767382) * 10^40
        + 5617709409193572961894169829395444699934) * 10^40
        + 9776267184744799371011826931150449798190) * 10^40
        + 5407055368151398016926533125916893618263) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((10533 * 10^40
        + 3547305472757256638233770310330474179941) * 10^40
        + 5502041335962061623454794851416459042531) * 10^40
        + 7237511254108429468372399130419192560668) * 10^40
        + 7233148914441778526117190471873336569229)) : ℚ) /
        (((45382245358777912581104592172631068 * 10^40
        + 3445296212612626449243005841447441373604) * 10^40
        + 4273527942609141406040578168096750486992) * 10^40
        + 6608223103170383329677423513941254864896)))

noncomputable def corrSecondN02701PlusPointP015Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP015BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP015Center2575‖ ≤
          corrSecondN02701PlusPointP015Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP015Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP015Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP015Input2575 16 =
      (corrSecondN02701PlusPointP015Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP015Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP015Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP015Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP015Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP015Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP015Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP015DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP015Factor2575 * embedPair2542
          corrSecondN02701PlusPointP015Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP015Factor2575 : ℝ) *
            corrSecondN02701PlusPointP015Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP015Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP015Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP015BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP015Factor2575)

def corrSecondN02701PlusPointP016Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((483342473044070207188278171 : ℚ) /
        236118324143482260684800000000))

def corrSecondN02701PlusPointP016Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP016Factor2575 : RatPair2542 := (((((((((((4141 * 10^40
        + 3835201940887099432782569574005238902652) * 10^40
        + 7325043918436484717256542525044033923056) * 10^40
        + 9915147215218934264819550904678697578276) * 10^40
        + 9979453338370813453379429171639897729541) * 10^40
        + 2281664360038648108010669020827970733264) * 10^40
        + 1916820296281048534176593656908177694064) * 10^40
        + 7779468087409634366216848790524396074600) * 10^40
        + 1196793093200963226890360899604275605207) : ℚ) /
        (((((((51488704845107984685253312531 * 10^40
        + 5394920186289725437701525670988833332619) * 10^40
        + 3813655210585682173747927669104580534375) * 10^40
        + 7477188023329442545959672763995327566458) * 10^40
        + 879829570802611619807760171030909897797) * 10^40
        + 3002811525272852673356573894568916827016) * 10^40
        + 8940433960810508796110496535231484005275) * 10^40
        + 7265557613342240466584529996596803272704)),
    (((-((((1858 * 10^40
        + 8861174955550796297861565166536685270684) * 10^40
        + 2508965473702727337811323826332603148343) * 10^40
        + 5780428454640169964514201986169977202165) * 10^40
        + 8384116494654571968672284817361616965521)) : ℚ) /
        (((7563707559796318763517432028771844 * 10^40
        + 7240882702102104408207167640241240228934) * 10^40
        + 712254657101523567673429694682791747832) * 10^40
        + 1101370517195063888279570585656875810816)))

noncomputable def corrSecondN02701PlusPointP016Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP016BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP016Center2575‖ ≤
          corrSecondN02701PlusPointP016Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP016Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP016Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP016Input2575 16 =
      (corrSecondN02701PlusPointP016Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP016Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP016Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP016Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP016Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP016Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP016Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP016DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP016Factor2575 * embedPair2542
          corrSecondN02701PlusPointP016Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP016Factor2575 : ℝ) *
            corrSecondN02701PlusPointP016Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP016Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP016Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP016BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP016Factor2575)

def corrSecondN02701PlusPointP017Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1071059113331693339029979313 : ℚ) /
        472236648286964521369600000000))

def corrSecondN02701PlusPointP017Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP017Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5340807675552299768977550017622244998396) * 10^40
        + 5758133202398479479969573331612171959615) * 10^40
        + 3601135636961017816997093326533752101090) * 10^40
        + 467464948392519485862121938036517961288) * 10^40
        + 3869818494268038931029509346797316288640) * 10^40
        + 1976742054049196778791093720761050894237) * 10^40
        + 3963464684369988857299566323154048749967) * 10^40
        + 4371577014318077161807671738915990072783) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((4119 * 10^40
        + 1846937230567472193551016132177675651413) * 10^40
        + 6574239230841009081181065876905439873377) * 10^40
        + 8956247576242891602579139450673986361377) * 10^40
        + 6771385111604410522994086528129898721363)) : ℚ) /
        (((15127415119592637527034864057543689 * 10^40
        + 4481765404204208816414335280482480457868) * 10^40
        + 1424509314203047135346859389365583495664) * 10^40
        + 2202741034390127776559141171313751621632)))

noncomputable def corrSecondN02701PlusPointP017Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP017BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP017Center2575‖ ≤
          corrSecondN02701PlusPointP017Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP017Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP017Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP017Input2575 16 =
      (corrSecondN02701PlusPointP017Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP017Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP017Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP017Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP017Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP017Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP017Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP017DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP017Factor2575 * embedPair2542
          corrSecondN02701PlusPointP017Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP017Factor2575 : ℝ) *
            corrSecondN02701PlusPointP017Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP017Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP017Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP017BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP017Factor2575)

def corrSecondN02701PlusPointP018Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((277630191250842385602313847 : ℚ) /
        118059162071741130342400000000))

def corrSecondN02701PlusPointP018Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP018Factor2575 : RatPair2542 := (((((((((((1035 * 10^40
        + 3458800477495906018223763938391684803379) * 10^40
        + 8348540847194108752916749163164456021652) * 10^40
        + 938023003403566744745844808867328861016) * 10^40
        + 1262530436420597287526576332308961445785) * 10^40
        + 8777987718394294710831664846696284811422) * 10^40
        + 8155186025782506236780497821201082413600) * 10^40
        + 620920766378161540901125551905426080051) * 10^40
        + 1440703709179703363840606988271610845663) : ℚ) /
        (((((((12872176211276996171313328132 * 10^40
        + 8848730046572431359425381417747208333154) * 10^40
        + 8453413802646420543436981917276145133593) * 10^40
        + 9369297005832360636489918190998831891614) * 10^40
        + 5219957392700652904951940042757727474449) * 10^40
        + 3250702881318213168339143473642229206754) * 10^40
        + 2235108490202627199027624133807871001318) * 10^40
        + 9316389403335560116646132499149200818176)),
    (((-((((3203 * 10^40
        + 2126520780933621936054864034868473422110) * 10^40
        + 1499810635052688284540659505448726578470) * 10^40
        + 6028409115437885222326122580984942624355) * 10^40
        + 3405432507546183779893767158403999233391)) : ℚ) /
        (((11345561339694478145276148043157767 * 10^40
        + 861324053153156612310751460361860343401) * 10^40
        + 1068381985652285351510144542024187621748) * 10^40
        + 1652055775792595832419355878485313716224)))

noncomputable def corrSecondN02701PlusPointP018Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP018BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP018Center2575‖ ≤
          corrSecondN02701PlusPointP018Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP018Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP018Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP018Input2575 16 =
      (corrSecondN02701PlusPointP018Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP018Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP018Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP018Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP018Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP018Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP018Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP018DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP018Factor2575 * embedPair2542
          corrSecondN02701PlusPointP018Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP018Factor2575 : ℝ) *
            corrSecondN02701PlusPointP018Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP018Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP018Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP018BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP018Factor2575)

def corrSecondN02701PlusPointP019Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((59091935462568230097122829 : ℚ) /
        23611832414348226068480000000))

def corrSecondN02701PlusPointP019Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP019Factor2575 : RatPair2542 := (((((((((((1035 * 10^40
        + 3458800473268418725052378101669336739859) * 10^40
        + 8124885174551838186084557176882031495312) * 10^40
        + 6861716454205899067418423032945233183366) * 10^40
        + 2759165694191063309830024564486299465375) * 10^40
        + 1513769964303768469073842726074412340213) * 10^40
        + 2896108177268804758902897009096165646778) * 10^40
        + 9234427013303832115966241294398728923479) * 10^40
        + 3068444117857418185957378473506641830319) : ℚ) /
        (((((((12872176211276996171313328132 * 10^40
        + 8848730046572431359425381417747208333154) * 10^40
        + 8453413802646420543436981917276145133593) * 10^40
        + 9369297005832360636489918190998831891614) * 10^40
        + 5219957392700652904951940042757727474449) * 10^40
        + 3250702881318213168339143473642229206754) * 10^40
        + 2235108490202627199027624133807871001318) * 10^40
        + 9316389403335560116646132499149200818176)),
    (((-((((1136 * 10^40
        + 3079453323347766329842110600633655965666) * 10^40
        + 8925112619324267952276139195818137770941) * 10^40
        + 2577437148264666943324714886484380450113) * 10^40
        + 1447063699935852187196292021709806427395)) : ℚ) /
        (((3781853779898159381758716014385922 * 10^40
        + 3620441351051052204103583820120620114467) * 10^40
        + 356127328550761783836714847341395873916) * 10^40
        + 550685258597531944139785292828437905408)))

noncomputable def corrSecondN02701PlusPointP019Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP019BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP019Center2575‖ ≤
          corrSecondN02701PlusPointP019Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP019Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP019Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP019Input2575 16 =
      (corrSecondN02701PlusPointP019Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP019Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP019Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP019Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP019Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP019Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP019Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP019DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP019Factor2575 * embedPair2542
          corrSecondN02701PlusPointP019Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP019Factor2575 : ℝ) *
            corrSecondN02701PlusPointP019Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP019Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP019Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP019BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP019Factor2575)

def corrSecondN02701PlusPointP020Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1259391271552815101014882561 : ℚ) /
        472236648286964521369600000000))

def corrSecondN02701PlusPointP020Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP020Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5340807493965155016335558867026663941415) * 10^40
        + 8332691971565870762952055406525584900111) * 10^40
        + 7497629888213051566798851480584616725928) * 10^40
        + 404678545288714010077192521440651221088) * 10^40
        + 355797534668808451554203205827890862836) * 10^40
        + 5481022389590569386804870583944716304418) * 10^40
        + 3153712201260121832775383121059407706813) * 10^40
        + 4966412025276587605387294363846547514415) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((14530 * 10^40
        + 4732053072590860645860709467114404197200) * 10^40
        + 7784794219942421515399274544441864070461) * 10^40
        + 2375340267827063793574052198063425133500) * 10^40
        + 9292970550266083925849760710329791244233)) : ℚ) /
        (((45382245358777912581104592172631068 * 10^40
        + 3445296212612626449243005841447441373604) * 10^40
        + 4273527942609141406040578168096750486992) * 10^40
        + 6608223103170383329677423513941254864896)))

noncomputable def corrSecondN02701PlusPointP020Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP020BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP020Center2575‖ ≤
          corrSecondN02701PlusPointP020Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP020Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP020Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP020Input2575 16 =
      (corrSecondN02701PlusPointP020Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP020Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP020Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP020Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP020Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP020Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP020Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP020DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP020Factor2575 * embedPair2542
          corrSecondN02701PlusPointP020Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP020Factor2575 : ℝ) *
            corrSecondN02701PlusPointP020Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP020Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP020Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP020BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP020Factor2575)

def corrSecondN02701PlusPointP021Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1324111916357314294844085153 : ℚ) /
        472236648286964521369600000000))

def corrSecondN02701PlusPointP021Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP021Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5340807424786423788685426963825085296831) * 10^40
        + 2196886276245750235420353507179061290638) * 10^40
        + 8945377220232475473797254747105951521274) * 10^40
        + 3818464296026475853124476529675956683517) * 10^40
        + 4986177749981214881788912735864339487998) * 10^40
        + 304250956504593739061738382651240988710) * 10^40
        + 7801177950235320516631321701444770606275) * 10^40
        + 1854300881018105068074705469182212867823) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((5092 * 10^40
        + 4001026134196417551945218294531027699050) * 10^40
        + 490598360391681808835486651148681790773) * 10^40
        + 7186339777421953114610707598598916298811) * 10^40
        + 2592708326900277590431120240368450471203)) : ℚ) /
        (((15127415119592637527034864057543689 * 10^40
        + 4481765404204208816414335280482480457868) * 10^40
        + 1424509314203047135346859389365583495664) * 10^40
        + 2202741034390127776559141171313751621632)))

noncomputable def corrSecondN02701PlusPointP021Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP021BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP021Center2575‖ ≤
          corrSecondN02701PlusPointP021Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP021Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP021Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP021Input2575 16 =
      (corrSecondN02701PlusPointP021Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP021Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP021Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP021Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP021Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP021Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP021Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP021DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP021Factor2575 * embedPair2542
          corrSecondN02701PlusPointP021Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP021Factor2575 : ℝ) *
            corrSecondN02701PlusPointP021Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP021Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP021Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP021BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP021Factor2575)

def corrSecondN02701PlusPointP022Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((271447665815041436069447627 : ℚ) /
        94447329657392904273920000000))

def corrSecondN02701PlusPointP022Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP022Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5340807388037154327597489763011712445021) * 10^40
        + 1784837841995861048612444275717990467961) * 10^40
        + 8965565358473591764724963165825790511614) * 10^40
        + 6613316630959698584998938781767309196314) * 10^40
        + 4005780549370509608903116966057242426170) * 10^40
        + 5926260264455225580896162596668940551726) * 10^40
        + 6093592814911725544711873323508576526675) * 10^40
        + 983521463961182802927031195886007763679) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((15659 * 10^40
        + 4027760150640626181697241124536096687829) * 10^40
        + 7778990268633866551043139479342809724239) * 10^40
        + 538417035346978905933073030600356645651) * 10^40
        + 4365210054302054550293651296944402268655)) : ℚ) /
        (((45382245358777912581104592172631068 * 10^40
        + 3445296212612626449243005841447441373604) * 10^40
        + 4273527942609141406040578168096750486992) * 10^40
        + 6608223103170383329677423513941254864896)))

noncomputable def corrSecondN02701PlusPointP022Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP022BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP022Center2575‖ ≤
          corrSecondN02701PlusPointP022Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP022Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP022Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP022Input2575 16 =
      (corrSecondN02701PlusPointP022Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP022Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP022Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP022Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP022Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP022Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP022Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP022DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP022Factor2575 * embedPair2542
          corrSecondN02701PlusPointP022Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP022Factor2575 : ℝ) *
            corrSecondN02701PlusPointP022Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP022Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP022Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP022BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP022Factor2575)

def corrSecondN02701PlusPointP023Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((726373966280652557447321527 : ℚ) /
        236118324143482260684800000000))

def corrSecondN02701PlusPointP023Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP023Factor2575 : RatPair2542 := (((((((((((4141 * 10^40
        + 3835201819249765362175918385870082544380) * 10^40
        + 3858148715362388459725195903903658236035) * 10^40
        + 7270366369351952414540260654020111072109) * 10^40
        + 5761816116790692974037317392682635755040) * 10^40
        + 7715153051244836270751552876020241445701) * 10^40
        + 9636834114653156223744264112420104136806) * 10^40
        + 9457919692357522212264888357624969673573) * 10^40
        + 4680797214993762222795591275974577592415) : ℚ) /
        (((((((51488704845107984685253312531 * 10^40
        + 5394920186289725437701525670988833332619) * 10^40
        + 3813655210585682173747927669104580534375) * 10^40
        + 7477188023329442545959672763995327566458) * 10^40
        + 879829570802611619807760171030909897797) * 10^40
        + 3002811525272852673356573894568916827016) * 10^40
        + 8940433960810508796110496535231484005275) * 10^40
        + 7265557613342240466584529996596803272704)),
    (((-((((8380 * 10^40
        + 6817567189673375220265816215582968373394) * 10^40
        + 2034117315878139663094739884617305639953) * 10^40
        + 5250321595289172729101598239646495536317) * 10^40
        + 7893279946294599405880295903514765920431)) : ℚ) /
        (((22691122679388956290552296086315534 * 10^40
        + 1722648106306313224621502920723720686802) * 10^40
        + 2136763971304570703020289084048375243496) * 10^40
        + 3304111551585191664838711756970627432448)))

noncomputable def corrSecondN02701PlusPointP023Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP023BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP023Center2575‖ ≤
          corrSecondN02701PlusPointP023Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP023Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP023Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP023Input2575 16 =
      (corrSecondN02701PlusPointP023Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP023Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP023Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP023Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP023Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP023Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP023Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP023DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP023Factor2575 * embedPair2542
          corrSecondN02701PlusPointP023Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP023Factor2575 : ℝ) *
            corrSecondN02701PlusPointP023Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP023Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP023Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP023BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP023Factor2575)

def corrSecondN02701PlusPointP024Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((748320139291177557999687593 : ℚ) /
        236118324143482260684800000000))

def corrSecondN02701PlusPointP024Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP024Factor2575 : RatPair2542 := (((((((((((4141 * 10^40
        + 3835201805859736957553463028469202733823) * 10^40
        + 2221126004581183133152902843971327328124) * 10^40
        + 6579242757949056939105147392957604557861) * 10^40
        + 343922579409182608041985264258003789168) * 10^40
        + 5446491764298431729008306415034924274687) * 10^40
        + 7453762962217956537780648708388633506853) * 10^40
        + 759150312516353723709526546163454748400) * 10^40
        + 6875845655134038721693024115205397599135) : ℚ) /
        (((((((51488704845107984685253312531 * 10^40
        + 5394920186289725437701525670988833332619) * 10^40
        + 3813655210585682173747927669104580534375) * 10^40
        + 7477188023329442545959672763995327566458) * 10^40
        + 879829570802611619807760171030909897797) * 10^40
        + 3002811525272852673356573894568916827016) * 10^40
        + 8940433960810508796110496535231484005275) * 10^40
        + 7265557613342240466584529996596803272704)),
    (((-((((8633 * 10^40
        + 8900217685458111760722885418232363847165) * 10^40
        + 4968845343531712793455419020692038548650) * 10^40
        + 6767465858909297227620434639535857013272) * 10^40
        + 4740375636504677262946812745465247082929)) : ℚ) /
        (((22691122679388956290552296086315534 * 10^40
        + 1722648106306313224621502920723720686802) * 10^40
        + 2136763971304570703020289084048375243496) * 10^40
        + 3304111551585191664838711756970627432448)))

noncomputable def corrSecondN02701PlusPointP024Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP024BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP024Center2575‖ ≤
          corrSecondN02701PlusPointP024Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP024Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP024Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP024Input2575 16 =
      (corrSecondN02701PlusPointP024Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP024Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP024Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP024Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP024Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP024Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP024Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP024DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP024Factor2575 * embedPair2542
          corrSecondN02701PlusPointP024Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP024Factor2575 : ℝ) *
            corrSecondN02701PlusPointP024Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP024Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP024Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP024BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP024Factor2575)

def corrSecondN02701PlusPointP025Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((24244894162688885003625027 : ℚ) /
        7378697629483820646400000000))

def corrSecondN02701PlusPointP025Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP025Factor2575 : RatPair2542 := (((((((((((4 * 10^40
        + 443198439246589835357185037903363747397) * 10^40
        + 5486577133134114248080450801146629301509) * 10^40
        + 8349676581586318857497087279468710425868) * 10^40
        + 1511377541873388103677287896872169048802) * 10^40
        + 6271744588148635840808694046572895142647) * 10^40
        + 2532324584394226456247345905665128005514) * 10^40
        + 7358642913567707975080108540232950434595) * 10^40
        + 3673841129203868636033109571319770714663) : ℚ) /
        (((((((50281938325300766294192688 * 10^40
        + 190815351744423559997755396163075032551) * 10^40
        + 3861146147666587580247800710614359941928) * 10^40
        + 1013161316429032658736288742933589187076) * 10^40
        + 6192265458565236925409968515792022372947) * 10^40
        + 676760558130149270188824779193914957838) * 10^40
        + 8836855892539854012496201656772686996098) * 10^40
        + 9020767146106779531705648955074801565696)),
    (((-((((93 * 10^40
        + 2434033684892659442853652607501245285563) * 10^40
        + 8189665744685096227099085620284506966833) * 10^40
        + 3642242865031071748795182101116776508936) * 10^40
        + 8004842373606170104382335016338093251977)) : ℚ) /
        (((236365861243634961359919750899120 * 10^40
        + 1476277584440690762756473988757538757154) * 10^40
        + 1897257958034422611489794677958837242119) * 10^40
        + 7534417828662345746508736580801777369088)))

noncomputable def corrSecondN02701PlusPointP025Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP025BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP025Center2575‖ ≤
          corrSecondN02701PlusPointP025Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP025Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP025Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP025Input2575 16 =
      (corrSecondN02701PlusPointP025Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP025Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP025Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP025Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP025Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP025Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP025Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP025DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP025Factor2575 * embedPair2542
          corrSecondN02701PlusPointP025Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP025Factor2575 : ℝ) *
            corrSecondN02701PlusPointP025Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP025Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP025Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP025BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP025Factor2575)

def corrSecondN02701PlusPointP026Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((50247333217324293119390103 : ℚ) /
        14757395258967641292800000000))

def corrSecondN02701PlusPointP026Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP026Factor2575 : RatPair2542 := (((((((((((16 * 10^40
        + 1772793756914562118835256753777597835237) * 10^40
        + 7940356706061717876124188742296427896148) * 10^40
        + 4730683175453391555057676632928974587382) * 10^40
        + 8991388481971934530673319580771402174158) * 10^40
        + 8955656438993855471923680292312593534282) * 10^40
        + 4852493058765323899989695906236463402599) * 10^40
        + 3038679593640538443384997981931689673424) * 10^40
        + 1820320065539530575754411314453171946015) : ℚ) /
        (((((((201127753301203065176770752 * 10^40
        + 763261406977694239991021584652300130205) * 10^40
        + 5444584590666350320991202842457439767712) * 10^40
        + 4052645265716130634945154971734356748306) * 10^40
        + 4769061834260947701639874063168089491788) * 10^40
        + 2707042232520597080755299116775659831355) * 10^40
        + 5347423570159416049984806627090747984395) * 10^40
        + 6083068584427118126822595820299206262784)),
    (((-((((193 * 10^40
        + 2461460930643185655046051761979987201555) * 10^40
        + 7583955518169432513767609826423079663019) * 10^40
        + 5347742563564566077898710284011988669945) * 10^40
        + 647503390155706679213177728868699883653)) : ℚ) /
        (((472731722487269922719839501798240 * 10^40
        + 2952555168881381525512947977515077514308) * 10^40
        + 3794515916068845222979589355917674484239) * 10^40
        + 5068835657324691493017473161603554738176)))

noncomputable def corrSecondN02701PlusPointP026Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP026BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP026Center2575‖ ≤
          corrSecondN02701PlusPointP026Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP026Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP026Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP026Input2575 16 =
      (corrSecondN02701PlusPointP026Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP026Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP026Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP026Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP026Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP026Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP026Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP026DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP026Factor2575 * embedPair2542
          corrSecondN02701PlusPointP026Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP026Factor2575 : ℝ) *
            corrSecondN02701PlusPointP026Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP026Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP026Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP026BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP026Factor2575)

def corrSecondN02701PlusPointP027Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((105567055574838531593598713 : ℚ) /
        29514790517935282585600000000))

def corrSecondN02701PlusPointP027Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP027Factor2575 : RatPair2542 := (((((((((((64 * 10^40
        + 7091175027225803710212539842984232299304) * 10^40
        + 984549560592372484972434050631589729018) * 10^40
        + 5951871114347168049873161758279389116194) * 10^40
        + 6711413768129907573820303272936627585589) * 10^40
        + 5817345938588808863666670228549113151454) * 10^40
        + 6375127513206176744047923244920212373878) * 10^40
        + 8140946793421583172101331042050005160486) * 10^40
        + 4488848829492215589740732491616290603263) : ℚ) /
        (((((((804511013204812260707083008 * 10^40
        + 3053045627910776959964086338609200520822) * 10^40
        + 1778338362665401283964811369829759070849) * 10^40
        + 6210581062864522539780619886937426993225) * 10^40
        + 9076247337043790806559496252672357967153) * 10^40
        + 828168930082388323021196467102639325422) * 10^40
        + 1389694280637664199939226508362991937582) * 10^40
        + 4332274337708472507290383281196825051136)),
    (((-((((1218 * 10^40
        + 5587159929510373915087814356396460572) * 10^40
        + 2629308428009636263060245411539927812734) * 10^40
        + 5713813994313364408682528090571297069114) * 10^40
        + 9684475483446092927115063580263112892289)) : ℚ) /
        (((2836390334923619536319037010789441 * 10^40
        + 7715331013288289153077687865090465085850) * 10^40
        + 2767095496413071337877536135506046905437) * 10^40
        + 413013943948148958104838969621328429056)))

noncomputable def corrSecondN02701PlusPointP027Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP027BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP027Center2575‖ ≤
          corrSecondN02701PlusPointP027Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP027Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP027Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP027Input2575 16 =
      (corrSecondN02701PlusPointP027Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP027Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP027Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP027Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP027Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP027Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP027Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP027DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP027Factor2575 * embedPair2542
          corrSecondN02701PlusPointP027Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP027Factor2575 : ℝ) *
            corrSecondN02701PlusPointP027Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP027Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP027Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP027BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP027Factor2575)

def corrSecondN02701PlusPointP028Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((430301136886435135522330613 : ℚ) /
        118059162071741130342400000000))

def corrSecondN02701PlusPointP028Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP028Factor2575 : RatPair2542 := (((((((((((1035 * 10^40
        + 3458800432779356702273971862876645073263) * 10^40
        + 9746434259903088534792230407999713599397) * 10^40
        + 4894175342962457099389947009850081777022) * 10^40
        + 1810570314153145814238123347273601615736) * 10^40
        + 9064150593579141700265571967612409969352) * 10^40
        + 8706220569821893414210697049840372061314) * 10^40
        + 1039929960794352617217733364259551332227) * 10^40
        + 2081934875657899779088021476781321530423) : ℚ) /
        (((((((12872176211276996171313328132 * 10^40
        + 8848730046572431359425381417747208333154) * 10^40
        + 8453413802646420543436981917276145133593) * 10^40
        + 9369297005832360636489918190998831891614) * 10^40
        + 5219957392700652904951940042757727474449) * 10^40
        + 3250702881318213168339143473642229206754) * 10^40
        + 2235108490202627199027624133807871001318) * 10^40
        + 9316389403335560116646132499149200818176)),
    (((-((((451 * 10^40
        + 3348689650069951617649895181766725849963) * 10^40
        + 6035362427638770125160551475528114602294) * 10^40
        + 2632025015418000133459433717985740422938) * 10^40
        + 2456504162059891443194191220570098802999)) : ℚ) /
        (((1031414667244952558661468003923433 * 10^40
        + 3714665823013923328391886496396532758491) * 10^40
        + 97125635059298668319104049274926147431) * 10^40
        + 6513823252344781439310850534407755792384)))

noncomputable def corrSecondN02701PlusPointP028Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP028BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP028Center2575‖ ≤
          corrSecondN02701PlusPointP028Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP028Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP028Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP028Input2575 16 =
      (corrSecondN02701PlusPointP028Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP028Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP028Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP028Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP028Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP028Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP028Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP028DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP028Factor2575 * embedPair2542
          corrSecondN02701PlusPointP028Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP028Factor2575 : ℝ) *
            corrSecondN02701PlusPointP028Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP028Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP028Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP028BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP028Factor2575)

def corrSecondN02701PlusPointP029Input2575 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((442530733595656525480647121 : ℚ) /
        118059162071741130342400000000))

def corrSecondN02701PlusPointP029Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701PlusPointP029Factor2575 : RatPair2542 := (((((((((((1035 * 10^40
        + 3458800428363006678307173473803702131547) * 10^40
        + 5053737858732473105940555165620271571544) * 10^40
        + 5727445800630465238012193735234929508448) * 10^40
        + 1077770070492238796162216308619762771248) * 10^40
        + 5333192098558570920824753490628818960038) * 10^40
        + 7219823058222134644011215644292204909295) * 10^40
        + 8837632766805436253097698452500218487611) * 10^40
        + 5948688837851875733749335816999093720975) : ℚ) /
        (((((((12872176211276996171313328132 * 10^40
        + 8848730046572431359425381417747208333154) * 10^40
        + 8453413802646420543436981917276145133593) * 10^40
        + 9369297005832360636489918190998831891614) * 10^40
        + 5219957392700652904951940042757727474449) * 10^40
        + 3250702881318213168339143473642229206754) * 10^40
        + 2235108490202627199027624133807871001318) * 10^40
        + 9316389403335560116646132499149200818176)),
    (((-((((5105 * 10^40
        + 7849234641050870162504862766230066158212) * 10^40
        + 6238646934469492556191936563558357329935) * 10^40
        + 9589857518743168114505838540598257461515) * 10^40
        + 407104740223143667601556952428347525913)) : ℚ) /
        (((11345561339694478145276148043157767 * 10^40
        + 861324053153156612310751460361860343401) * 10^40
        + 1068381985652285351510144542024187621748) * 10^40
        + 1652055775792595832419355878485313716224)))

noncomputable def corrSecondN02701PlusPointP029Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701PlusPointP029BaseError2575 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP029Center2575‖ ≤
          corrSecondN02701PlusPointP029Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701PlusPointP029Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701PlusPointP029Input2575]
  have hs : compactExp2547 corrSecondN02701PlusPointP029Input2575 16 =
      (corrSecondN02701PlusPointP029Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701PlusPointP029Input2575 16).2 : ℝ) =
      corrSecondN02701PlusPointP029Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701PlusPointP029Error2575]
  have h := compactExp_error2547 corrSecondN02701PlusPointP029Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      corrSecondN02701PlusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701PlusPointP029Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701PlusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701PlusPointP029Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701PlusPointP029DerivativeError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP029Factor2575 * embedPair2542
          corrSecondN02701PlusPointP029Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701PlusPointP029Factor2575 : ℝ) *
            corrSecondN02701PlusPointP029Error2575 := by
  have hx : |corrSecondN02701PlusPointPosition2575| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701PlusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) corrSecondN02701PlusPointPosition2575 = embedPair2542
          corrSecondN02701PlusPointP029Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701PlusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701PlusPointP029Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701PlusPointP029BaseError2575
    (embedPair_magnitude2542 corrSecondN02701PlusPointP029Factor2575)

theorem corrSecondN02701PlusPointGrid2575 :
    -stripRadius2303 + (2701 : ℝ) * (2 * stripRadius2303 / 10240) =
      corrSecondN02701PlusPointPosition2575 := by
  norm_num [stripRadius2303, corrSecondN02701PlusPointPosition2575]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP000DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP001DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP002DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP003DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP004DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP005DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP006DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP007DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP008DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP009DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP010DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP011DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP012DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP013DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP014DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP015DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP016DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP017DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP018DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP019DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP020DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP021DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP022DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP023DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP024DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP025DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP026DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP027DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP028DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointP029DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPointGrid2575
