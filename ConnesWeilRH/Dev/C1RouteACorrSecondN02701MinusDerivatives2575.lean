import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def corrSecondN02701MinusPointPosition2575 : ℝ := (((-158531586419) : ℝ) /
        51200000000)

theorem corrSecondN02701MinusPointZero2575 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def corrSecondN02701MinusPointP000Center2575 : RatPair2542 := (0, 0)

def corrSecondN02701MinusPointP000Factor2575 : RatPair2542 := (0, 0)

noncomputable def corrSecondN02701MinusPointP000Error2575 : ℝ := 0

theorem corrSecondN02701MinusPointP000Exterior2575 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02701MinusPointPosition2575 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |corrSecondN02701MinusPointPosition2575| := by
    norm_num [storedWidth, corrSecondN02701MinusPointPosition2575]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem corrSecondN02701MinusPointP000BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP000Center2575‖ ≤
          corrSecondN02701MinusPointP000Error2575 := by
  rw [corrSecondN02701MinusPointP000Exterior2575]
  norm_num [corrSecondN02701MinusPointP000Center2575, corrSecondN02701MinusPointP000Error2575,
      corrSecondN02701MinusPointZero2575]

theorem corrSecondN02701MinusPointP000DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP000Factor2575 * embedPair2542
          corrSecondN02701MinusPointP000Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP000Factor2575 : ℝ) *
            corrSecondN02701MinusPointP000Error2575 := by
  rw [corrSecondN02701MinusPointP000Exterior2575]
  norm_num [corrSecondN02701MinusPointP000Factor2575, corrSecondN02701MinusPointP000Center2575,
      corrSecondN02701MinusPointP000Error2575,
      corrSecondN02701MinusPointZero2575, pairMagnitude2542]

def corrSecondN02701MinusPointP001Input2575 : RatPair2542 := ((((-((334 * 10^40
        + 4181679957483969025469344287059963590135) * 10^40
        + 8161414014029282377368998074593359799021)) : ℚ) /
        ((941 * 10^40
        + 6102169216506454849034257242358098754684) * 10^40
        + 4000368461807982441421667880140800000000)),
    ((875774620147323865939848151 : ℚ) /
        3689348814741910323200000000))

def corrSecondN02701MinusPointP001Center2575 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP001Factor2575 : RatPair2542 :=
    ((((((((((7428459297909450910046568364225 * 10^40
        + 7702110732210090121356870499267192622394) * 10^40
        + 6447358604740260558785329987258312527312) * 10^40
        + 1128475796371190865024480850304540443431) * 10^40
        + 6589766311637747739839349058813867730107) * 10^40
        + 4631006780441877228014241616962406691484) * 10^40
        + 1114791247221968174706088353986568184292) * 10^40
        + 143786272899663997451429330051967632855) : ℚ) /
        (((((((20607464985904378613958700 * 10^40
        + 2595159148890025498073864656791828969138) * 10^40
        + 3290271723839544840116734095165196842913) * 10^40
        + 467218176066478541785588708334274916834) * 10^40
        + 5928978601939523898086459863702066739961) * 10^40
        + 1122900486430430706333686109357355611694) * 10^40
        + 7954245854741826417223689275212605633229) * 10^40
        + 4940715927363866938280641064052010778624)),
    (((-(((21566254419275175081238878033058112968 * 10^40
        + 4279118592658037454987622346089910948300) * 10^40
        + 9592971090431787152843099106729535358129) * 10^40
        + 7059631829506515188681741654817506969651)) : ℚ) /
        (((453954457912953847599410478691028 * 10^40
        + 1779924909704564993115249489169742548465) * 10^40
        + 2128249869612705703746351004084215377754) * 10^40
        + 876988830001680477006235447041424621568)))

noncomputable def corrSecondN02701MinusPointP001Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP001BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP001Center2575‖ ≤
          corrSecondN02701MinusPointP001Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP001Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP001Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP001Input2575 9 =
      (corrSecondN02701MinusPointP001Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP001Input2575 9).2 : ℝ) =
      corrSecondN02701MinusPointP001Error2575 := by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP001Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP001Input2575 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          corrSecondN02701MinusPointP001Input2575)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP001Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP001DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP001Factor2575 * embedPair2542
          corrSecondN02701MinusPointP001Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP001Factor2575 : ℝ) *
            corrSecondN02701MinusPointP001Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP001Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP001Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP001BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP001Factor2575)

def corrSecondN02701MinusPointP002Input2575 : RatPair2542 := ((((-((8590 * 10^40
        + 1599478870791053102602381735213025077527) * 10^40
        + 4292607931183293216346445262371930612461)) : ℚ) /
        ((36680 * 10^40
        + 5267114824128922047222362789138794665314) * 10^40
        + 902751818529719531373343041126400000000)),
    (((-875774620147323865939848151) : ℚ) /
        1844674407370955161600000000))

def corrSecondN02701MinusPointP002Center2575 : RatPair2542 := ((((-7432742102829368094385) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-11177578774756275941739) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def corrSecondN02701MinusPointP002Factor2575 : RatPair2542 :=
    ((((((((((66509337332020077703071674352144778 *
    10^40
        + 9507000639300047551622134067808912983954) * 10^40
        + 7046779277983758689853085413196735709204) * 10^40
        + 2416321281047688367602550562057307562638) * 10^40
        + 1932032506659111976059306267769028641981) * 10^40
        + 7513329173212692136521176671171980187494) * 10^40
        + 4655862609758228803289677553583590846823) * 10^40
        + 82337836701874463428995363479058269655) : ℚ) /
        (((((((759280344898816204453149405320788 * 10^40
        + 2562755322010977854069761205418464326627) * 10^40
        + 5898745153495915958343318913963452743824) * 10^40
        + 3252926811272942913028468180398675049644) * 10^40
        + 9236371670745830152415062103830109362394) * 10^40
        + 2100223503579552350555864490642376213996) * 10^40
        + 8684472799811869662047026269274168847585) * 10^40
        + 5890140663961686575747173712578387902464)),
    (((((8914932412946733821501706857859867158473 * 10^40
        + 8539382482683942891064847545205193103724) * 10^40
        + 8284077989395940201434228160743222677011) * 10^40
        + 1052412709335242977308761209423141652531) : ℚ) /
        (((2755504209575474781138380549191462978 * 10^40
        + 6825593386581207281056339534128529847042) * 10^40
        + 7275016703069080889991558353505182267414) * 10^40
        + 7315590532715512968354674442604703121408)))

noncomputable def corrSecondN02701MinusPointP002Error2575 : ℝ := ((49382499124458385033 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP002BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP002Center2575‖ ≤
          corrSecondN02701MinusPointP002Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP002Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP002Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP002Input2575 8 =
      (corrSecondN02701MinusPointP002Center2575, ((49382499124458385033 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP002Input2575 8).2 : ℝ) =
      corrSecondN02701MinusPointP002Error2575 := by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP002Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP002Input2575 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          corrSecondN02701MinusPointP002Input2575)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP002Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP002DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP002Factor2575 * embedPair2542
          corrSecondN02701MinusPointP002Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP002Factor2575 : ℝ) *
            corrSecondN02701MinusPointP002Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP002Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP002Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP002BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP002Factor2575)

def corrSecondN02701MinusPointP003Input2575 : RatPair2542 := ((((-((1123649 * 10^40
        + 8976927238487000191863367108472502773987) * 10^40
        + 3331593634587051799526484294029501456047)) : ℚ) /
        ((6644764 * 10^40
        + 348595898346936727630550565694213304645) * 10^40
        + 356964576015918677191939509452800000000)),
    (((-875774620147323865939848151) : ℚ) /
        1844674407370955161600000000))

def corrSecondN02701MinusPointP003Center2575 : RatPair2542 := ((((-128031342998015805707829314715)
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-192537343849641036358254016761) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def corrSecondN02701MinusPointP003Factor2575 : RatPair2542 := ((((-((((((((1003326 * 10^40
        + 1042561288285493422867069488236711006761) * 10^40
        + 3817998729779492346736568674084083651769) * 10^40
        + 9123660916198433355633415848157783203084) * 10^40
        + 1993546732972530910874582726116558190771) * 10^40
        + 5813545985381127118448810463964362639949) * 10^40
        + 2993907016699567290102769749767039976724) * 10^40
        + 8446608306577690348825196220769113410633) * 10^40
        + 355317143266800264942566357875711590305)) : ℚ) /
        ((((((((735 * 10^40
        + 9031578952271773711277727944517603986909) * 10^40
        + 4299908468254782876318386098252753667384) * 10^40
        + 8035978194544546520050508311085649632775) * 10^40
        + 400074100802200631812660752661470157903) * 10^40
        + 5226728248472081247871991151670895911425) * 10^40
        + 8584895352049947641835514097188246337603) * 10^40
        + 3382474669940090816110002118475276189617) * 10^40
        + 8499698954555383858007879986387213090816)),
    ((((((29443 * 10^40
        + 1045635574423311950006285830181687183972) * 10^40
        + 4060406802912608689850728263899343801150) * 10^40
        + 6179104476838324711124118966703664871217) * 10^40
        + 2707226680740890497010450338899857564497) : ℚ) /
        ((((27 * 10^40
        + 1275350501151721831636617526493081859830) * 10^40
        + 371775513702883693023963091771403332187) * 10^40
        + 5225040598366931331057220453837234929427) * 10^40
        + 5352048433052554802286703513941254864896)))

noncomputable def corrSecondN02701MinusPointP003Error2575 : ℝ := ((797028780675931752600253645 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP003BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP003Center2575‖ ≤
          corrSecondN02701MinusPointP003Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP003Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP003Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP003Input2575 8 =
      (corrSecondN02701MinusPointP003Center2575, ((797028780675931752600253645 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP003Input2575 8).2 : ℝ) =
      corrSecondN02701MinusPointP003Error2575 := by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP003Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP003Input2575 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          corrSecondN02701MinusPointP003Input2575)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP003Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP003DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP003Factor2575 * embedPair2542
          corrSecondN02701MinusPointP003Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP003Factor2575 : ℝ) *
            corrSecondN02701MinusPointP003Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP003Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP003Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP003BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP003Factor2575)

def corrSecondN02701MinusPointP004Input2575 : RatPair2542 := ((((-((19409 * 10^40
        + 4221726842157504765492452247847422161138) * 10^40
        + 1088311962520617223323074241864118112461)) : ℚ) /
        ((134028 * 10^40
        + 5763226050861645114137505055527745988340) * 10^40
        + 4359916327702839531373343041126400000000)),
    ((875774620147323865939848151 : ℚ) /
        1844674407370955161600000000))

def corrSecondN02701MinusPointP004Center2575 : RatPair2542 :=
    ((((-64207546511769766768481979511471) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((96557219279266825819155349428839 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def corrSecondN02701MinusPointP004Factor2575 : RatPair2542 :=
    ((((-(((((((203191405743370464006832348233386018822 *
    10^40
        + 5458095736479673803325373137881813309360) * 10^40
        + 1430006692139843898271215018925057722385) * 10^40
        + 72310306354369087643579970678527823029) * 10^40
        + 2961967661095982238324920581528938496974) * 10^40
        + 5378650891029965458632038371550252872071) * 10^40
        + 7966678330640978823169944409511117229381) * 10^40
        + 3408044669003840585223869382614691730345)) : ℚ) /
        (((((((135347276887106627857315383444605739 * 10^40
        + 9991691964880965341918750282532925631821) * 10^40
        + 7593644714309317200092186362824769527439) * 10^40
        + 6382506515583507680681236206264303987138) * 10^40
        + 2902368533592603132790791778952058210570) * 10^40
        + 6226284060945507959518899118947584203178) * 10^40
        + 9302318401510404933239847161850597735717) * 10^40
        + 4009126728727183218511973712578387902464)),
    (((-((((1 * 10^40
        + 9260285336551290801459516111217722847885) * 10^40
        + 9513042083472812360843075093051914934136) * 10^40
        + 8853796692398610858810283655778368104532) * 10^40
        + 6043013362343193420801863406688766652531)) : ℚ) /
        (((36789574187139843526753432905043948801 * 10^40
        + 9159438194521168849766900670326046515891) * 10^40
        + 7851531537127144730886893054125014016304) * 10^40
        + 366335614660560978287474442604703121408)))

noncomputable def corrSecondN02701MinusPointP004Error2575 : ℝ := ((97529468585144800089090291783 :
    ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem corrSecondN02701MinusPointP004BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP004Center2575‖ ≤
          corrSecondN02701MinusPointP004Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP004Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP004Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP004Input2575 8 =
      (corrSecondN02701MinusPointP004Center2575, ((97529468585144800089090291783 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP004Input2575 8).2 : ℝ) =
      corrSecondN02701MinusPointP004Error2575 := by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP004Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP004Input2575 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          corrSecondN02701MinusPointP004Input2575)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP004Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP004DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP004Factor2575 * embedPair2542
          corrSecondN02701MinusPointP004Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP004Factor2575 : ℝ) *
            corrSecondN02701MinusPointP004Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP004Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP004Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP004BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP004Factor2575)

def corrSecondN02701MinusPointP005Center2575 : RatPair2542 := (0, 0)

def corrSecondN02701MinusPointP005Factor2575 : RatPair2542 := (0, 0)

noncomputable def corrSecondN02701MinusPointP005Error2575 : ℝ := 0

theorem corrSecondN02701MinusPointP005Exterior2575 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02701MinusPointPosition2575 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |corrSecondN02701MinusPointPosition2575| := by
    norm_num [storedWidth, corrSecondN02701MinusPointPosition2575]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem corrSecondN02701MinusPointP005BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP005Center2575‖ ≤
          corrSecondN02701MinusPointP005Error2575 := by
  rw [corrSecondN02701MinusPointP005Exterior2575]
  norm_num [corrSecondN02701MinusPointP005Center2575, corrSecondN02701MinusPointP005Error2575,
      corrSecondN02701MinusPointZero2575]

theorem corrSecondN02701MinusPointP005DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP005Factor2575 * embedPair2542
          corrSecondN02701MinusPointP005Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP005Factor2575 : ℝ) *
            corrSecondN02701MinusPointP005Error2575 := by
  rw [corrSecondN02701MinusPointP005Exterior2575]
  norm_num [corrSecondN02701MinusPointP005Factor2575, corrSecondN02701MinusPointP005Center2575,
      corrSecondN02701MinusPointP005Error2575,
      corrSecondN02701MinusPointZero2575, pairMagnitude2542]

def corrSecondN02701MinusPointP006Input2575 : RatPair2542 :=
    ((((-42061326624915781747488640051599353) : ℚ) /
        73447401531966028759865753600000000),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP006Center2575 : RatPair2542 := (((21384329496406693 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP006Factor2575 : RatPair2542 := (((((1771029968943 * 10^40
        + 8819068004564837363755976274454744592167) * 10^40
        + 2662024971598155755545470189049347426649) : ℚ) /
        ((354951109 * 10^40
        + 6805509743719437539166977228721393891763) * 10^40
        + 5385343191475503022181880756197389706596)),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP006Error2575 : ℝ := ((3767500786445 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem corrSecondN02701MinusPointP006BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP006Center2575‖ ≤
          corrSecondN02701MinusPointP006Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP006Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP006Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP006Input2575 7 =
      (corrSecondN02701MinusPointP006Center2575, ((3767500786445 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP006Input2575 7).2 : ℝ) =
      corrSecondN02701MinusPointP006Error2575 := by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP006Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP006Input2575 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          corrSecondN02701MinusPointP006Input2575)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP006Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP006DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP006Factor2575 * embedPair2542
          corrSecondN02701MinusPointP006Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP006Factor2575 : ℝ) *
            corrSecondN02701MinusPointP006Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP006Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP006Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP006BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP006Factor2575)

def corrSecondN02701MinusPointP007Input2575 : RatPair2542 := ((((-((1123649 * 10^40
        + 8976927238487000191863367108472502773987) * 10^40
        + 3331593634587051799526484294029501456047)) : ℚ) /
        ((1661191 * 10^40
        + 87148974586734181907637641423553326161) * 10^40
        + 2589241144003979669297984877363200000000)),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP007Center2575 : RatPair2542 := (((231219924674649256075727664923 :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP007Factor2575 : RatPair2542 := ((((((((((263583363409526855 * 10^40
        + 3390267172578361847356314565575982655861) * 10^40
        + 5956912016380360686113464939667812691966) * 10^40
        + 3339364638319793618476904006700611102476) * 10^40
        + 4111317600686352312536160059192196848958) * 10^40
        + 6905363319728587524752549813452120202875) * 10^40
        + 7087667050648418293638296276619387058959) * 10^40
        + 8387946182701606409141049106826999073849) : ℚ) /
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

noncomputable def corrSecondN02701MinusPointP007Error2575 : ℝ := ((16000632657409328590635391 : ℝ)
    /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem corrSecondN02701MinusPointP007BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP007Center2575‖ ≤
          corrSecondN02701MinusPointP007Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP007Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP007Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP007Input2575 6 =
      (corrSecondN02701MinusPointP007Center2575, ((16000632657409328590635391 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP007Input2575 6).2 : ℝ) =
      corrSecondN02701MinusPointP007Error2575 := by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP007Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP007Input2575 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          corrSecondN02701MinusPointP007Input2575)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP007Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP007DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP007Factor2575 * embedPair2542
          corrSecondN02701MinusPointP007Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP007Factor2575 : ℝ) *
            corrSecondN02701MinusPointP007Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP007Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP007Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP007BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP007Factor2575)

def corrSecondN02701MinusPointP008Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((630729240492097551551105443 : ℚ) /
        944473296573929042739200000000))

def corrSecondN02701MinusPointP008Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP008Factor2575 : RatPair2542 := (((((((((((66262 * 10^40
        + 1316502988854836934695249509350342953732) * 10^40
        + 464751784223516618640958228062636019117) * 10^40
        + 4258170318006329560300335369919489454610) * 10^40
        + 296681080790446917884531004649815423718) * 10^40
        + 8127578077918553194001139598635075205470) * 10^40
        + 6308882961857667544299514840465380930299) * 10^40
        + 1828811248794964578222068210368939239958) * 10^40
        + 6394943733193919033149710370851493158375) : ℚ) /
        (((((((823819277521727754964053000504 * 10^40
        + 6318722980635607003224410735821333321910) * 10^40
        + 1018483369370914779966842705673288550011) * 10^40
        + 9635008373271080735354764223925241063329) * 10^40
        + 4077273132841785916924162736494558364756) * 10^40
        + 8044984404365642773705182313102669232270) * 10^40
        + 3046943372968140737767944563703744084411) * 10^40
        + 6248921813475847465352479945548852363264)),
    (((-((((7277 * 10^40
        + 1617627075356380610252946202040223159030) * 10^40
        + 571628721818109266049309607924899484835) * 10^40
        + 3963579434374738151451211871379110745365) * 10^40
        + 5812440895212074285306345216997181046021)) : ℚ) /
        (((90764490717555825162209184345262136 * 10^40
        + 6890592425225252898486011682894882747208) * 10^40
        + 8547055885218282812081156336193500973985) * 10^40
        + 3216446206340766659354847027882509729792)))

noncomputable def corrSecondN02701MinusPointP008Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP008BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP008Center2575‖ ≤
          corrSecondN02701MinusPointP008Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP008Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP008Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP008Input2575 16 =
      (corrSecondN02701MinusPointP008Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP008Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP008Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP008Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP008Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP008Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP008Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP008DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP008Factor2575 * embedPair2542
          corrSecondN02701MinusPointP008Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP008Factor2575 : ℝ) *
            corrSecondN02701MinusPointP008Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP008Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP008Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP008BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP008Factor2575)

def corrSecondN02701MinusPointP009Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((938059634128117561826070909 : ℚ) /
        944473296573929042739200000000))

def corrSecondN02701MinusPointP009Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP009Factor2575 : RatPair2542 := (((((((((((66262 * 10^40
        + 1316502789378783006550647415573113386641) * 10^40
        + 5298454055198288856745533871248422921479) * 10^40
        + 4518890868510257304148295907367963132027) * 10^40
        + 2592620482364388945081691021036153302233) * 10^40
        + 2710619354008342360616916417696843018487) * 10^40
        + 6270709238138431887359826332694629543624) * 10^40
        + 6565701187567756974162767016412845806092) * 10^40
        + 3618099552754852310928917685634407096487) : ℚ) /
        (((((((823819277521727754964053000504 * 10^40
        + 6318722980635607003224410735821333321910) * 10^40
        + 1018483369370914779966842705673288550011) * 10^40
        + 9635008373271080735354764223925241063329) * 10^40
        + 4077273132841785916924162736494558364756) * 10^40
        + 8044984404365642773705182313102669232270) * 10^40
        + 3046943372968140737767944563703744084411) * 10^40
        + 6248921813475847465352479945548852363264)),
    (((-((((3607 * 10^40
        + 6820619523751181244648529964978023449283) * 10^40
        + 3142578995433169852687601605964006211944) * 10^40
        + 3208591687191334684885950330054607357295) * 10^40
        + 4859146202738992157152904776762175738441)) : ℚ) /
        (((30254830239185275054069728115087378 * 10^40
        + 8963530808408417632828670560964960915736) * 10^40
        + 2849018628406094270693718778731166991328) * 10^40
        + 4405482068780255553118282342627503243264)))

noncomputable def corrSecondN02701MinusPointP009Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP009BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP009Center2575‖ ≤
          corrSecondN02701MinusPointP009Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP009Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP009Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP009Input2575 16 =
      (corrSecondN02701MinusPointP009Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP009Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP009Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP009Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP009Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP009Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP009Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP009DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP009Factor2575 * embedPair2542
          corrSecondN02701MinusPointP009Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP009Factor2575 : ℝ) *
            corrSecondN02701MinusPointP009Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP009Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP009Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP009BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP009Factor2575)

def corrSecondN02701MinusPointP010Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((558025679572758329216722299 : ℚ) /
        472236648286964521369600000000))

def corrSecondN02701MinusPointP010Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP010Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5329125659527921332546341646514578891276) * 10^40
        + 8393312322952245501749741687879874195314) * 10^40
        + 5109485499770466908174383831631606808221) * 10^40
        + 3771742145014183222149268627588616419413) * 10^40
        + 8032516450535227545715182573274426881336) * 10^40
        + 3064973167415364010283052807495150385696) * 10^40
        + 6011374016968601230938000478782207890555) * 10^40
        + 3866565746654554423628338684038330790295) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((2146 * 10^40
        + 1100777186514674560855626113419535997871) * 10^40
        + 3169876937059389026631672570904452463427) * 10^40
        + 2105946718570163108588918878823643628041) * 10^40
        + 6203602156431708743530822479099797625551)) : ℚ) /
        (((15127415119592637527034864057543689 * 10^40
        + 4481765404204208816414335280482480457868) * 10^40
        + 1424509314203047135346859389365583495664) * 10^40
        + 2202741034390127776559141171313751621632)))

noncomputable def corrSecondN02701MinusPointP010Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP010BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP010Center2575‖ ≤
          corrSecondN02701MinusPointP010Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP010Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP010Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP010Input2575 16 =
      (corrSecondN02701MinusPointP010Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP010Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP010Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP010Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP010Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP010Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP010Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP010DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP010Factor2575 * embedPair2542
          corrSecondN02701MinusPointP010Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP010Factor2575 : ℝ) *
            corrSecondN02701MinusPointP010Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP010Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP010Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP010BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP010Factor2575)

def corrSecondN02701MinusPointP011Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((617361885721254929729880619 : ℚ) /
        472236648286964521369600000000))

def corrSecondN02701MinusPointP011Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP011Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5329125630672885225302168849658396338388) * 10^40
        + 1181075918708605375453738311088777380129) * 10^40
        + 3688262448527003881973488029887200256740) * 10^40
        + 7724695945358606508597740254397275252745) * 10^40
        + 5825020558841363707264792494150770364519) * 10^40
        + 2336583271260079607935700706336653724254) * 10^40
        + 2780869112712511725151587899466119339603) * 10^40
        + 2841732025777886047626541260301427502455) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((7122 * 10^40
        + 9332970492340987280995260385145547945416) * 10^40
        + 4998185420892351647855290974455410044958) * 10^40
        + 6342825773613051765435709130971392208660) * 10^40
        + 7800949584801826417490770359066565765693)) : ℚ) /
        (((45382245358777912581104592172631068 * 10^40
        + 3445296212612626449243005841447441373604) * 10^40
        + 4273527942609141406040578168096750486992) * 10^40
        + 6608223103170383329677423513941254864896)))

noncomputable def corrSecondN02701MinusPointP011Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP011BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP011Center2575‖ ≤
          corrSecondN02701MinusPointP011Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP011Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP011Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP011Input2575 16 =
      (corrSecondN02701MinusPointP011Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP011Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP011Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP011Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP011Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP011Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP011Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP011DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP011Factor2575 * embedPair2542
          corrSecondN02701MinusPointP011Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP011Factor2575 : ℝ) *
            corrSecondN02701MinusPointP011Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP011Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP011Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP011BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP011Factor2575)

def corrSecondN02701MinusPointP012Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((13576393469632358173878271 : ℚ) /
        9444732965739290427392000000))

def corrSecondN02701MinusPointP012Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP012Factor2575 : RatPair2542 := (((((((((((4141 * 10^40
        + 3832281399428670694447577441965813085651) * 10^40
        + 1592369334138284564782445026958305396897) * 10^40
        + 4521751731247719836270163959400235942360) * 10^40
        + 5828618757067500768081243048077390419409) * 10^40
        + 6090701175962063275703185979779248323824) * 10^40
        + 8841042395991884444887860529080229429818) * 10^40
        + 3440008189871310346617341252952666468363) * 10^40
        + 2312778973308880163857354408111219087551) : ℚ) /
        (((((((51488704845107984685253312531 * 10^40
        + 5394920186289725437701525670988833332619) * 10^40
        + 3813655210585682173747927669104580534375) * 10^40
        + 7477188023329442545959672763995327566458) * 10^40
        + 879829570802611619807760171030909897797) * 10^40
        + 3002811525272852673356573894568916827016) * 10^40
        + 8940433960810508796110496535231484005275) * 10^40
        + 7265557613342240466584529996596803272704)),
    (((-((((3916 * 10^40
        + 72615152019869500482486493297101786116) * 10^40
        + 1899147430685112744963130936077768256511) * 10^40
        + 2838553891683684526090824223357529817972) * 10^40
        + 336683278740106528510947045311036203425)) : ℚ) /
        (((22691122679388956290552296086315534 * 10^40
        + 1722648106306313224621502920723720686802) * 10^40
        + 2136763971304570703020289084048375243496) * 10^40
        + 3304111551585191664838711756970627432448)))

noncomputable def corrSecondN02701MinusPointP012Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP012BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP012Center2575‖ ≤
          corrSecondN02701MinusPointP012Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP012Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP012Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP012Input2575 16 =
      (corrSecondN02701MinusPointP012Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP012Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP012Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP012Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP012Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP012Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP012Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP012DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP012Factor2575 * embedPair2542
          corrSecondN02701MinusPointP012Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP012Factor2575 : ℝ) *
            corrSecondN02701MinusPointP012Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP012Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP012Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP012BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP012Factor2575)

def corrSecondN02701MinusPointP013Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((146965053600227290725850929 : ℚ) /
        94447329657392904273920000000))

def corrSecondN02701MinusPointP013Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP013Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5329125564958558468276628122404751215127) * 10^40
        + 6167072497705280992349571101444281163369) * 10^40
        + 6368993585742979501833065372318975132083) * 10^40
        + 4898986775995698309079537556391605671754) * 10^40
        + 1844993913940891085102439808644722442679) * 10^40
        + 798412935749262428680319217436771021320) * 10^40
        + 6978609327237351331051803644771064766668) * 10^40
        + 3280639242421670715092898167635043943479) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((2826 * 10^40
        + 633349830062816035923270725077363338663) * 10^40
        + 4219255598506418521253387182167500391427) * 10^40
        + 1486722050875816115847578339590964110842) * 10^40
        + 5329359902249138424982131558200224507105)) : ℚ) /
        (((15127415119592637527034864057543689 * 10^40
        + 4481765404204208816414335280482480457868) * 10^40
        + 1424509314203047135346859389365583495664) * 10^40
        + 2202741034390127776559141171313751621632)))

noncomputable def corrSecondN02701MinusPointP013Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP013BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP013Center2575‖ ≤
          corrSecondN02701MinusPointP013Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP013Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP013Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP013Input2575 16 =
      (corrSecondN02701MinusPointP013Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP013Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP013Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP013Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP013Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP013Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP013Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP013DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP013Factor2575 * embedPair2542
          corrSecondN02701MinusPointP013Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP013Factor2575 : ℝ) *
            corrSecondN02701MinusPointP013Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP013Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP013Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP013BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP013Factor2575)

def corrSecondN02701MinusPointP014Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((838597898629083505249081609 : ℚ) /
        472236648286964521369600000000))

def corrSecondN02701MinusPointP014Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP014Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5329125497404861424198806105492849648383) * 10^40
        + 7417134203308343829111792628344055786924) * 10^40
        + 2800908643450691092182356750760128028161) * 10^40
        + 7219079691007069882289823032529104799902) * 10^40
        + 1646720939588351935641644736097290401050) * 10^40
        + 9382269002519992515207279331034504374245) * 10^40
        + 4095156891103957358791084555643346309626) * 10^40
        + 8725656428158471623112682698451291914975) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((9675 * 10^40
        + 4869925313326930862899639977503701410842) * 10^40
        + 6116671082071426830050759841708678255572) * 10^40
        + 8524285261249075072561073224059176070130) * 10^40
        + 3480957263542787175928581061782426698223)) : ℚ) /
        (((45382245358777912581104592172631068 * 10^40
        + 3445296212612626449243005841447441373604) * 10^40
        + 4273527942609141406040578168096750486992) * 10^40
        + 6608223103170383329677423513941254864896)))

noncomputable def corrSecondN02701MinusPointP014Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP014BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP014Center2575‖ ≤
          corrSecondN02701MinusPointP014Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP014Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP014Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP014Input2575 16 =
      (corrSecondN02701MinusPointP014Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP014Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP014Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP014Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP014Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP014Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP014Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP014DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP014Factor2575 * embedPair2542
          corrSecondN02701MinusPointP014Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP014Factor2575 : ℝ) *
            corrSecondN02701MinusPointP014Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP014Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP014Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP014BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP014Factor2575)

def corrSecondN02701MinusPointP015Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((912951341665564226630614693 : ℚ) /
        472236648286964521369600000000))

def corrSecondN02701MinusPointP015Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP015Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5329125443522801549327825359583432692794) * 10^40
        + 7076261226187624793318786116677106742136) * 10^40
        + 5450569843562828536943835900519692839856) * 10^40
        + 5377364452802959029065312370328219126730) * 10^40
        + 509816319026872211329891773410804598186) * 10^40
        + 7127517616279173881983553589515145648782) * 10^40
        + 5319473400742818955449887472496456023963) * 10^40
        + 5694742341017958016926533125916893618263) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((10533 * 10^40
        + 3543591506065304301551020658671319589628) * 10^40
        + 4400961169173926694160882476332596114010) * 10^40
        + 1567238265822340176797170372345425622326) * 10^40
        + 9668496636436941473882809528126663430771)) : ℚ) /
        (((45382245358777912581104592172631068 * 10^40
        + 3445296212612626449243005841447441373604) * 10^40
        + 4273527942609141406040578168096750486992) * 10^40
        + 6608223103170383329677423513941254864896)))

noncomputable def corrSecondN02701MinusPointP015Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP015BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP015Center2575‖ ≤
          corrSecondN02701MinusPointP015Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP015Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP015Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP015Input2575 16 =
      (corrSecondN02701MinusPointP015Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP015Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP015Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP015Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP015Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP015Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP015Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP015DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP015Factor2575 * embedPair2542
          corrSecondN02701MinusPointP015Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP015Factor2575 : ℝ) *
            corrSecondN02701MinusPointP015Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP015Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP015Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP015BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP015Factor2575)

def corrSecondN02701MinusPointP016Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((483342473044070207188278171 : ℚ) /
        236118324143482260684800000000))

def corrSecondN02701MinusPointP016Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP016Factor2575 : RatPair2542 := (((((((((((4141 * 10^40
        + 3832281350433965858275572988096187314007) * 10^40
        + 1167377560907975860364072996455552111945) * 10^40
        + 4157324665228177591460000256623414180746) * 10^40
        + 574245650336342017719666226308948113470) * 10^40
        + 2818582214601366253841203309197108190965) * 10^40
        + 2294272348052448764198939596938102931276) * 10^40
        + 6665269641409139262326363925860897631043) * 10^40
        + 3768714836417603226890360899604275605207) : ℚ) /
        (((((((51488704845107984685253312531 * 10^40
        + 5394920186289725437701525670988833332619) * 10^40
        + 3813655210585682173747927669104580534375) * 10^40
        + 7477188023329442545959672763995327566458) * 10^40
        + 879829570802611619807760171030909897797) * 10^40
        + 3002811525272852673356573894568916827016) * 10^40
        + 8940433960810508796110496535231484005275) * 10^40
        + 7265557613342240466584529996596803272704)),
    (((-((((1858 * 10^40
        + 8860519528927358886078502119965108071292) * 10^40
        + 8805672938583944419129246510943620933280) * 10^40
        + 4818879698397126325634002678914411298910) * 10^40
        + 3596747901346708031327715182638383034479)) : ℚ) /
        (((7563707559796318763517432028771844 * 10^40
        + 7240882702102104408207167640241240228934) * 10^40
        + 712254657101523567673429694682791747832) * 10^40
        + 1101370517195063888279570585656875810816)))

noncomputable def corrSecondN02701MinusPointP016Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP016BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP016Center2575‖ ≤
          corrSecondN02701MinusPointP016Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP016Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP016Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP016Input2575 16 =
      (corrSecondN02701MinusPointP016Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP016Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP016Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP016Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP016Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP016Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP016Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP016DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP016Factor2575 * embedPair2542
          corrSecondN02701MinusPointP016Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP016Factor2575 : ℝ) *
            corrSecondN02701MinusPointP016Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP016Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP016Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP016BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP016Factor2575)

def corrSecondN02701MinusPointP017Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1071059113331693339029979313 : ℚ) /
        472236648286964521369600000000))

def corrSecondN02701MinusPointP017Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP017Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5329125313739765470949563673986038643814) * 10^40
        + 1127467772284444052399695217258244715169) * 10^40
        + 569845436997991123558890734312618510966) * 10^40
        + 2846634196254633743223070156712719497004) * 10^40
        + 6017489912518911514351646500273866119444) * 10^40
        + 3486550261134797698880477480880751843084) * 10^40
        + 9506670900368008441737626864500054975740) * 10^40
        + 4659263987184637161807671738915990072783) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((4119 * 10^40
        + 1845484842876956005675754439913153968868) * 10^40
        + 6514799339574155509039319067914541504650) * 10^40
        + 1733445737938096450794366248091809452227) * 10^40
        + 7192814410863429477005913471870101278637)) : ℚ) /
        (((15127415119592637527034864057543689 * 10^40
        + 4481765404204208816414335280482480457868) * 10^40
        + 1424509314203047135346859389365583495664) * 10^40
        + 2202741034390127776559141171313751621632)))

noncomputable def corrSecondN02701MinusPointP017Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP017BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP017Center2575‖ ≤
          corrSecondN02701MinusPointP017Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP017Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP017Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP017Input2575 16 =
      (corrSecondN02701MinusPointP017Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP017Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP017Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP017Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP017Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP017Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP017Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP017DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP017Factor2575 * embedPair2542
          corrSecondN02701MinusPointP017Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP017Factor2575 : ℝ) *
            corrSecondN02701MinusPointP017Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP017Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP017Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP017BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP017Factor2575)

def corrSecondN02701MinusPointP018Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((277630191250842385602313847 : ℚ) /
        118059162071741130342400000000))

def corrSecondN02701MinusPointP018Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP018Factor2575 : RatPair2542 := (((((((((((1035 * 10^40
        + 3458070329882622624597014791914421906218) * 10^40
        + 4309124257811981538693631781017335568874) * 10^40
        + 1998567365905877576405957146853508011633) * 10^40
        + 3911228514411979428611635595976224041768) * 10^40
        + 1412217182034974247289298418788569175848) * 10^40
        + 749549038725356294286084306208563722903) * 10^40
        + 342371154878037764928504335739551469161) * 10^40
        + 9583684144983863363840606988271610845663) : ℚ) /
        (((((((12872176211276996171313328132 * 10^40
        + 8848730046572431359425381417747208333154) * 10^40
        + 8453413802646420543436981917276145133593) * 10^40
        + 9369297005832360636489918190998831891614) * 10^40
        + 5219957392700652904951940042757727474449) * 10^40
        + 3250702881318213168339143473642229206754) * 10^40
        + 2235108490202627199027624133807871001318) * 10^40
        + 9316389403335560116646132499149200818176)),
    (((-((((3203 * 10^40
        + 2125391356794647719511607292035381884790) * 10^40
        + 2500078688378978400711477395404597076083) * 10^40
        + 6526355742888893906970287580328474065662) * 10^40
        + 5926065481696696220106232841596000766609)) : ℚ) /
        (((11345561339694478145276148043157767 * 10^40
        + 861324053153156612310751460361860343401) * 10^40
        + 1068381985652285351510144542024187621748) * 10^40
        + 1652055775792595832419355878485313716224)))

noncomputable def corrSecondN02701MinusPointP018Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP018BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP018Center2575‖ ≤
          corrSecondN02701MinusPointP018Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP018Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP018Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP018Input2575 16 =
      (corrSecondN02701MinusPointP018Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP018Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP018Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP018Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP018Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP018Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP018Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP018DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP018Factor2575 * embedPair2542
          corrSecondN02701MinusPointP018Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP018Factor2575 : ℝ) *
            corrSecondN02701MinusPointP018Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP018Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP018Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP018BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP018Factor2575)

def corrSecondN02701MinusPointP019Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((59091935462568230097122829 : ℚ) /
        23611832414348226068480000000))

def corrSecondN02701MinusPointP019Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP019Factor2575 : RatPair2542 := (((((((((((1035 * 10^40
        + 3458070325655135331425628955192073842698) * 10^40
        + 4085468585169710971861439794734911042534) * 10^40
        + 7922260816708209899078535370931412333983) * 10^40
        + 5407863772182445450915083828153562061357) * 10^40
        + 4147999427944448005531476298166696704638) * 10^40
        + 5490471190211654816408483494103646956081) * 10^40
        + 8955877401803708339993620078232854312590) * 10^40
        + 1211424553661578185957378473506641830319) : ℚ) /
        (((((((12872176211276996171313328132 * 10^40
        + 8848730046572431359425381417747208333154) * 10^40
        + 8453413802646420543436981917276145133593) * 10^40
        + 9369297005832360636489918190998831891614) * 10^40
        + 5219957392700652904951940042757727474449) * 10^40
        + 3250702881318213168339143473642229206754) * 10^40
        + 2235108490202627199027624133807871001318) * 10^40
        + 9316389403335560116646132499149200818176)),
    (((-((((1136 * 10^40
        + 3079052671326760499641670645110857796867) * 10^40
        + 6365382769231674493147914921265011448852) * 10^40
        + 6878655124616944606533935788445890234081) * 10^40
        + 6542043158457747812803707978290193572605)) : ℚ) /
        (((3781853779898159381758716014385922 * 10^40
        + 3620441351051052204103583820120620114467) * 10^40
        + 356127328550761783836714847341395873916) * 10^40
        + 550685258597531944139785292828437905408)))

noncomputable def corrSecondN02701MinusPointP019Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP019BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP019Center2575‖ ≤
          corrSecondN02701MinusPointP019Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP019Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP019Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP019Input2575 16 =
      (corrSecondN02701MinusPointP019Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP019Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP019Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP019Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP019Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP019Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP019Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP019DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP019Factor2575 * embedPair2542
          corrSecondN02701MinusPointP019Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP019Factor2575 : ℝ) *
            corrSecondN02701MinusPointP019Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP019Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP019Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP019BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP019Factor2575)

def corrSecondN02701MinusPointP020Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1259391271552815101014882561 : ℚ) /
        472236648286964521369600000000))

def corrSecondN02701MinusPointP020Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP020Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5329125132152620718307572523390457586833) * 10^40
        + 3702026541451835335382177292171657655665) * 10^40
        + 4466339688250024873360648888363483135804) * 10^40
        + 2783847793150828267438140740116852756804) * 10^40
        + 2503468952919681034876340359304440693640) * 10^40
        + 6990830596676170306894254344064417253265) * 10^40
        + 8696918417258141417213443662405413932586) * 10^40
        + 5254098998143147605387294363846547514415) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((14530 * 10^40
        + 4726929757665719678788786392470101654530) * 10^40
        + 6575502752674793822866803758036811842564) * 10^40
        + 6918521651037645348222072556637920053504) * 10^40
        + 9158765323843356074150239289670208755767)) : ℚ) /
        (((45382245358777912581104592172631068 * 10^40
        + 3445296212612626449243005841447441373604) * 10^40
        + 4273527942609141406040578168096750486992) * 10^40
        + 6608223103170383329677423513941254864896)))

noncomputable def corrSecondN02701MinusPointP020Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP020BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP020Center2575‖ ≤
          corrSecondN02701MinusPointP020Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP020Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP020Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP020Input2575 16 =
      (corrSecondN02701MinusPointP020Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP020Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP020Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP020Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP020Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP020Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP020Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP020DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP020Factor2575 * embedPair2542
          corrSecondN02701MinusPointP020Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP020Factor2575 : ℝ) *
            corrSecondN02701MinusPointP020Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP020Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP020Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP020BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP020Factor2575)

def corrSecondN02701MinusPointP021Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1324111916357314294844085153 : ℚ) /
        472236648286964521369600000000))

def corrSecondN02701MinusPointP021Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP021Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5329125062973889490657440620188878942248) * 10^40
        + 7566220846131714807850475392825134046192) * 10^40
        + 5914087020269448780359052154884817931150) * 10^40
        + 6197633543888590110485424748352158219233) * 10^40
        + 7133849168232087465111049889340889318802) * 10^40
        + 1814059163590194659151122142770941937558) * 10^40
        + 3344384166233340101069382242790776832048) * 10^40
        + 2141987853884665068074705469182212867823) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((5092 * 10^40
        + 3999230599454921359170418061387701187074) * 10^40
        + 5808091149545215986452936271773735011972) * 10^40
        + 5977726282770429493183198244626890115100) * 10^40
        + 7028831866338762409568879759631549528797)) : ℚ) /
        (((15127415119592637527034864057543689 * 10^40
        + 4481765404204208816414335280482480457868) * 10^40
        + 1424509314203047135346859389365583495664) * 10^40
        + 2202741034390127776559141171313751621632)))

noncomputable def corrSecondN02701MinusPointP021Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP021BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP021Center2575‖ ≤
          corrSecondN02701MinusPointP021Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP021Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP021Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP021Input2575 16 =
      (corrSecondN02701MinusPointP021Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP021Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP021Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP021Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP021Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP021Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP021Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP021DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP021Factor2575 * embedPair2542
          corrSecondN02701MinusPointP021Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP021Factor2575 : ℝ) *
            corrSecondN02701MinusPointP021Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP021Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP021Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP021BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP021Factor2575)

def corrSecondN02701MinusPointP022Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((271447665815041436069447627 : ℚ) /
        94447329657392904273920000000))

def corrSecondN02701MinusPointP022Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP022Factor2575 : RatPair2542 := (((((((((((16565 * 10^40
        + 5329125026224620029569503419375506090438) * 10^40
        + 7154172411881825621042566161364063223515) * 10^40
        + 5934275158510565071286760573604656921490) * 10^40
        + 8992485878821812842359887000443510732030) * 10^40
        + 6153451967621382192225254119533792256974) * 10^40
        + 7436068471540826500985546356788641500574) * 10^40
        + 1636799030909745129149933864854582752448) * 10^40
        + 1271208436827742802927031195886007763679) : ℚ) /
        (((((((205954819380431938741013250126 * 10^40
        + 1579680745158901750806102683955333330477) * 10^40
        + 5254620842342728694991710676418322137502) * 10^40
        + 9908752093317770183838691055981310265832) * 10^40
        + 3519318283210446479231040684123639591189) * 10^40
        + 2011246101091410693426295578275667308067) * 10^40
        + 5761735843242035184441986140925936021102) * 10^40
        + 9062230453368961866338119986387213090816)),
    (((-((((15659 * 10^40
        + 4022238785243396822833531607047614047144) * 10^40
        + 7228731216732093290421660640192498255023) * 10^40
        + 1778020336485338576542343889966429426223) * 10^40
        + 3454326912968345449706348703055597731345)) : ℚ) /
        (((45382245358777912581104592172631068 * 10^40
        + 3445296212612626449243005841447441373604) * 10^40
        + 4273527942609141406040578168096750486992) * 10^40
        + 6608223103170383329677423513941254864896)))

noncomputable def corrSecondN02701MinusPointP022Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP022BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP022Center2575‖ ≤
          corrSecondN02701MinusPointP022Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP022Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP022Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP022Input2575 16 =
      (corrSecondN02701MinusPointP022Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP022Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP022Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP022Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP022Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP022Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP022Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP022DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP022Factor2575 * embedPair2542
          corrSecondN02701MinusPointP022Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP022Factor2575 : ℝ) *
            corrSecondN02701MinusPointP022Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP022Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP022Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP022BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP022Factor2575)

def corrSecondN02701MinusPointP023Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((726373966280652557447321527 : ℚ) /
        236118324143482260684800000000))

def corrSecondN02701MinusPointP023Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP023Factor2575 : RatPair2542 := (((((((((((4141 * 10^40
        + 3832281228796631787668921799961030955734) * 10^40
        + 7700482357833879602832726375315176424924) * 10^40
        + 1512543819361195741180710005964827674578) * 10^40
        + 6356608428756221538377554447351686138969) * 10^40
        + 8252070905807554416582087164389378903403) * 10^40
        + 14286166424556453766610052450029374018) * 10^40
        + 8343721246357027108374403492961471230016) * 10^40
        + 7252718958210402222795591275974577592415) : ℚ) /
        (((((((51488704845107984685253312531 * 10^40
        + 5394920186289725437701525670988833332619) * 10^40
        + 3813655210585682173747927669104580534375) * 10^40
        + 7477188023329442545959672763995327566458) * 10^40
        + 879829570802611619807760171030909897797) * 10^40
        + 3002811525272852673356573894568916827016) * 10^40
        + 8940433960810508796110496535231484005275) * 10^40
        + 7265557613342240466584529996596803272704)),
    (((-((((8380 * 10^40
        + 6814612236223450946566810362346542522142) * 10^40
        + 5453338398728854514003958029876912313451) * 10^40
        + 8803512279954853688948086313558790917892) * 10^40
        + 4554987991415480594119704096485234079569)) : ℚ) /
        (((22691122679388956290552296086315534 * 10^40
        + 1722648106306313224621502920723720686802) * 10^40
        + 2136763971304570703020289084048375243496) * 10^40
        + 3304111551585191664838711756970627432448)))

noncomputable def corrSecondN02701MinusPointP023Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP023BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP023Center2575‖ ≤
          corrSecondN02701MinusPointP023Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP023Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP023Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP023Input2575 16 =
      (corrSecondN02701MinusPointP023Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP023Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP023Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP023Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP023Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP023Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP023Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP023DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP023Factor2575 * embedPair2542
          corrSecondN02701MinusPointP023Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP023Factor2575 : ℝ) *
            corrSecondN02701MinusPointP023Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP023Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP023Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP023BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP023Factor2575)

def corrSecondN02701MinusPointP024Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((748320139291177557999687593 : ℚ) /
        236118324143482260684800000000))

def corrSecondN02701MinusPointP024Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP024Factor2575 : RatPair2542 := (((((((((((4141 * 10^40
        + 3832281215406603383046466442560151145177) * 10^40
        + 6063459647052674276260433315382845517013) * 10^40
        + 821420207958300265745596744902321160330) * 10^40
        + 938714891374711172382222318927054173097) * 10^40
        + 5983409618861149874838840703404061732388) * 10^40
        + 7831215013989356767802994648418558744064) * 10^40
        + 9644951866515858619819041681499956304843) * 10^40
        + 9447767398350678721693024115205397599135) : ℚ) /
        (((((((51488704845107984685253312531 * 10^40
        + 5394920186289725437701525670988833332619) * 10^40
        + 3813655210585682173747927669104580534375) * 10^40
        + 7477188023329442545959672763995327566458) * 10^40
        + 879829570802611619807760171030909897797) * 10^40
        + 3002811525272852673356573894568916827016) * 10^40
        + 8940433960810508796110496535231484005275) * 10^40
        + 7265557613342240466584529996596803272704)),
    (((-((((8633 * 10^40
        + 8897173453038041922276460209437230864915) * 10^40
        + 6370446934709059529504195048995436738045) * 10^40
        + 1916191755569193477962605560035603930773) * 10^40
        + 3186128419590042737053187254534752917071)) : ℚ) /
        (((22691122679388956290552296086315534 * 10^40
        + 1722648106306313224621502920723720686802) * 10^40
        + 2136763971304570703020289084048375243496) * 10^40
        + 3304111551585191664838711756970627432448)))

noncomputable def corrSecondN02701MinusPointP024Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP024BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP024Center2575‖ ≤
          corrSecondN02701MinusPointP024Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP024Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP024Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP024Input2575 16 =
      (corrSecondN02701MinusPointP024Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP024Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP024Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP024Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP024Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP024Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP024Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP024DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP024Factor2575 * embedPair2542
          corrSecondN02701MinusPointP024Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP024Factor2575 : ℝ) *
            corrSecondN02701MinusPointP024Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP024Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP024Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP024BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP024Factor2575)

def corrSecondN02701MinusPointP025Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((24244894162688885003625027 : ℚ) /
        7378697629483820646400000000))

def corrSecondN02701MinusPointP025Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP025Factor2575 : RatPair2542 := (((((((((((4 * 10^40
        + 443195587107475447100830549049936939205) * 10^40
        + 5119235662081840313649891748872617112241) * 10^40
        + 1713194333002343509183259593288968938175) * 10^40
        + 2498286518740541940165901409620869293318) * 10^40
        + 1828909546990982245247981677713880628445) * 10^40
        + 7894021314913534464284477102872188479379) * 10^40
        + 2005992329147785616580215488607302486896) * 10^40
        + 5815024646531228636033109571319770714663) : ℚ) /
        (((((((50281938325300766294192688 * 10^40
        + 190815351744423559997755396163075032551) * 10^40
        + 3861146147666587580247800710614359941928) * 10^40
        + 1013161316429032658736288742933589187076) * 10^40
        + 6192265458565236925409968515792022372947) * 10^40
        + 676760558130149270188824779193914957838) * 10^40
        + 8836855892539854012496201656772686996098) * 10^40
        + 9020767146106779531705648955074801565696)),
    (((-((((93 * 10^40
        + 2434000808102385727959318482420268908499) * 10^40
        + 4881870570664294873681540992710896727041) * 10^40
        + 3578856894062853990786481181458987908337) * 10^40
        + 7904072491177189895617664983661906748023)) : ℚ) /
        (((236365861243634961359919750899120 * 10^40
        + 1476277584440690762756473988757538757154) * 10^40
        + 1897257958034422611489794677958837242119) * 10^40
        + 7534417828662345746508736580801777369088)))

noncomputable def corrSecondN02701MinusPointP025Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP025BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP025Center2575‖ ≤
          corrSecondN02701MinusPointP025Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP025Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP025Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP025Input2575 16 =
      (corrSecondN02701MinusPointP025Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP025Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP025Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP025Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP025Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP025Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP025Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP025DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP025Factor2575 * embedPair2542
          corrSecondN02701MinusPointP025Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP025Factor2575 : ℝ) *
            corrSecondN02701MinusPointP025Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP025Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP025Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP025BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP025Factor2575)

def corrSecondN02701MinusPointP026Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((50247333217324293119390103 : ℚ) /
        14757395258967641292800000000))

def corrSecondN02701MinusPointP026Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP026Factor2575 : RatPair2542 := (((((((((((16 * 10^40
        + 1772782348358104565809838798363890602469) * 10^40
        + 6470990821852622138401952533200379139073) * 10^40
        + 8184754181117490161802365888210008636611) * 10^40
        + 2939024389440549876627773631766203152221) * 10^40
        + 1184316274363241089680830816876535477476) * 10^40
        + 6299279980842555932138220695064705298057) * 10^40
        + 1628077255960849009385425775429097882629) * 10^40
        + 385054134848970575754411314453171946015) : ℚ) /
        (((((((201127753301203065176770752 * 10^40
        + 763261406977694239991021584652300130205) * 10^40
        + 5444584590666350320991202842457439767712) * 10^40
        + 4052645265716130634945154971734356748306) * 10^40
        + 4769061834260947701639874063168089491788) * 10^40
        + 2707042232520597080755299116775659831355) * 10^40
        + 5347423570159416049984806627090747984395) * 10^40
        + 6083068584427118126822595820299206262784)),
    (((-((((193 * 10^40
        + 2461392793780021216036622849920560047312) * 10^40
        + 5332124575594921650437217820735916005716) * 10^40
        + 7763465742519194764102257404692573299557) * 10^40
        + 5437152050699333320786822271131300116347)) : ℚ) /
        (((472731722487269922719839501798240 * 10^40
        + 2952555168881381525512947977515077514308) * 10^40
        + 3794515916068845222979589355917674484239) * 10^40
        + 5068835657324691493017473161603554738176)))

noncomputable def corrSecondN02701MinusPointP026Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP026BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP026Center2575‖ ≤
          corrSecondN02701MinusPointP026Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP026Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP026Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP026Input2575 16 =
      (corrSecondN02701MinusPointP026Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP026Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP026Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP026Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP026Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP026Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP026Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP026DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP026Factor2575 * embedPair2542
          corrSecondN02701MinusPointP026Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP026Factor2575 : ℝ) *
            corrSecondN02701MinusPointP026Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP026Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP026Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP026BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP026Factor2575)

def corrSecondN02701MinusPointP027Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((105567055574838531593598713 : ℚ) /
        29514790517935282585600000000))

def corrSecondN02701MinusPointP027Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP027Factor2575 : RatPair2542 := (((((((((((64 * 10^40
        + 7091129392999973498110868021329403368231) * 10^40
        + 5107086023755989534083489214247394700719) * 10^40
        + 9768155137003562476851918779403525313108) * 10^40
        + 2501957398004368957638119476915831497838) * 10^40
        + 4731985280066351334695272326804880924231) * 10^40
        + 2162275201515104872642022400233179955710) * 10^40
        + 2498537442702825436103042216039637997305) * 10^40
        + 8747785106729975589740732491616290603263) : ℚ) /
        (((((((804511013204812260707083008 * 10^40
        + 3053045627910776959964086338609200520822) * 10^40
        + 1778338362665401283964811369829759070849) * 10^40
        + 6210581062864522539780619886937426993225) * 10^40
        + 9076247337043790806559496252672357967153) * 10^40
        + 828168930082388323021196467102639325422) * 10^40
        + 1389694280637664199939226508362991937582) * 10^40
        + 4332274337708472507290383281196825051136)),
    (((-((((1218 * 10^40
        + 5157703823495846551044638656769257648) * 10^40
        + 3132220790441845339625110431743470218047) * 10^40
        + 8799687506184975730555642537980338971648) * 10^40
        + 4388978916533427072884936419736887107711)) : ℚ) /
        (((2836390334923619536319037010789441 * 10^40
        + 7715331013288289153077687865090465085850) * 10^40
        + 2767095496413071337877536135506046905437) * 10^40
        + 413013943948148958104838969621328429056)))

noncomputable def corrSecondN02701MinusPointP027Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP027BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP027Center2575‖ ≤
          corrSecondN02701MinusPointP027Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP027Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP027Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP027Input2575 16 =
      (corrSecondN02701MinusPointP027Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP027Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP027Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP027Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP027Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP027Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP027Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP027DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP027Factor2575 * embedPair2542
          corrSecondN02701MinusPointP027Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP027Factor2575 : ℝ) *
            corrSecondN02701MinusPointP027Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP027Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP027Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP027BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP027Factor2575)

def corrSecondN02701MinusPointP028Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((430301136886435135522330613 : ℚ) /
        118059162071741130342400000000))

def corrSecondN02701MinusPointP028Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP028Factor2575 : RatPair2542 := (((((((((((1035 * 10^40
        + 3458070285166073308647222716399382176102) * 10^40
        + 5707017670520961320569113025852593146619) * 10^40
        + 5954719705464767931050059347836260927639) * 10^40
        + 4459268392144527955323182610940864211719) * 10^40
        + 1698380057219821236723205539704694333778) * 10^40
        + 1300583582764743471716283534847853370617) * 10^40
        + 761380349294228841245112148093676721338) * 10^40
        + 224915311462059779088021476781321530423) : ℚ) /
        (((((((12872176211276996171313328132 * 10^40
        + 8848730046572431359425381417747208333154) * 10^40
        + 8453413802646420543436981917276145133593) * 10^40
        + 9369297005832360636489918190998831891614) * 10^40
        + 5219957392700652904951940042757727474449) * 10^40
        + 3250702881318213168339143473642229206754) * 10^40
        + 2235108490202627199027624133807871001318) * 10^40
        + 9316389403335560116646132499149200818176)),
    (((-((((451 * 10^40
        + 3348530513430853010481190270545041913473) * 10^40
        + 9326026638999118785042191755999794819544) * 10^40
        + 9337358754074110903685188590348006259647) * 10^40
        + 9136889440172428556805808779429901197001)) : ℚ) /
        (((1031414667244952558661468003923433 * 10^40
        + 3714665823013923328391886496396532758491) * 10^40
        + 97125635059298668319104049274926147431) * 10^40
        + 6513823252344781439310850534407755792384)))

noncomputable def corrSecondN02701MinusPointP028Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP028BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP028Center2575‖ ≤
          corrSecondN02701MinusPointP028Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP028Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP028Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP028Input2575 16 =
      (corrSecondN02701MinusPointP028Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP028Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP028Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP028Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP028Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP028Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP028Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP028DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP028Factor2575 * embedPair2542
          corrSecondN02701MinusPointP028Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP028Factor2575 : ℝ) *
            corrSecondN02701MinusPointP028Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP028Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP028Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP028BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP028Factor2575)

def corrSecondN02701MinusPointP029Input2575 : RatPair2542 := ((((-((385452 * 10^40
        + 8796881758225214713944895805329816445007) * 10^40
        + 4250609115476011780674148398033407706047)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((442530733595656525480647121 : ℚ) /
        118059162071741130342400000000))

def corrSecondN02701MinusPointP029Center2575 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrSecondN02701MinusPointP029Factor2575 : RatPair2542 := (((((((((((1035 * 10^40
        + 3458070280749723284680424327326439234386) * 10^40
        + 1014321269350345891717437783473151118766) * 10^40
        + 6787990163132776069672306073221108659065) * 10^40
        + 3726468148483620937247275572287025367230) * 10^40
        + 7967421562199250457282387062721103324463) * 10^40
        + 9814186071164984701516802129299686218598) * 10^40
        + 8559083155305312477125077236334343876722) * 10^40
        + 4091669273656035733749335816999093720975) : ℚ) /
        (((((((12872176211276996171313328132 * 10^40
        + 8848730046572431359425381417747208333154) * 10^40
        + 8453413802646420543436981917276145133593) * 10^40
        + 9369297005832360636489918190998831891614) * 10^40
        + 5219957392700652904951940042757727474449) * 10^40
        + 3250702881318213168339143473642229206754) * 10^40
        + 2235108490202627199027624133807871001318) * 10^40
        + 9316389403335560116646132499149200818176)),
    (((-((((5105 * 10^40
        + 7847434386941224995211620790544714894381) * 10^40
        + 8814649990033266832787129398433569907368) * 10^40
        + 7962689010363993617262803449674445570865) * 10^40
        + 2192623441188696332398443047571652474087)) : ℚ) /
        (((11345561339694478145276148043157767 * 10^40
        + 861324053153156612310751460361860343401) * 10^40
        + 1068381985652285351510144542024187621748) * 10^40
        + 1652055775792595832419355878485313716224)))

noncomputable def corrSecondN02701MinusPointP029Error2575 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrSecondN02701MinusPointP029BaseError2575 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP029Center2575‖ ≤
          corrSecondN02701MinusPointP029Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hz : ‖embedPair2542 corrSecondN02701MinusPointP029Input2575‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrSecondN02701MinusPointP029Input2575]
  have hs : compactExp2547 corrSecondN02701MinusPointP029Input2575 16 =
      (corrSecondN02701MinusPointP029Center2575, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrSecondN02701MinusPointP029Input2575 16).2 : ℝ) =
      corrSecondN02701MinusPointP029Error2575 :=
      by
    rw [hs]
    norm_num [corrSecondN02701MinusPointP029Error2575]
  have h := compactExp_error2547 corrSecondN02701MinusPointP029Input2575 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      corrSecondN02701MinusPointPosition2575 = Complex.exp ((2 : ℂ)^16 * embedPair2542
          corrSecondN02701MinusPointP029Input2575) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrSecondN02701MinusPointPosition2575, storedWidth,
        nodeModulation2541,
      embedPair2542, corrSecondN02701MinusPointP029Input2575, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrSecondN02701MinusPointP029DerivativeError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP029Factor2575 * embedPair2542
          corrSecondN02701MinusPointP029Center2575‖ ≤
        (pairMagnitude2542 corrSecondN02701MinusPointP029Factor2575 : ℝ) *
            corrSecondN02701MinusPointP029Error2575 := by
  have hx : |corrSecondN02701MinusPointPosition2575| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [corrSecondN02701MinusPointPosition2575, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) corrSecondN02701MinusPointPosition2575 = embedPair2542
          corrSecondN02701MinusPointP029Factor2575 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrSecondN02701MinusPointPosition2575, storedWidth, nodeModulation2541, embedPair2542,
      corrSecondN02701MinusPointP029Factor2575, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrSecondN02701MinusPointP029BaseError2575
    (embedPair_magnitude2542 corrSecondN02701MinusPointP029Factor2575)

theorem corrSecondN02701MinusPointGrid2575 :
    -stripRadius2303 + (2701 : ℝ) * (2 * stripRadius2303 / 10240) =
      corrSecondN02701MinusPointPosition2575 := by
  norm_num [stripRadius2303, corrSecondN02701MinusPointPosition2575]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP000DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP001DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP002DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP003DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP004DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP005DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP006DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP007DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP008DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP009DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP010DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP011DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP012DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP013DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP014DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP015DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP016DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP017DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP018DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP019DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP020DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP021DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP022DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP023DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP024DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP025DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP026DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP027DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP028DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointP029DerivativeError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPointGrid2575
