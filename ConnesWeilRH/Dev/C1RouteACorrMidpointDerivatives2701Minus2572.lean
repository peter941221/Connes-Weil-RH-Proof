import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def corrC02701MinusMidpointPosition2572 : ℝ := (((-316997636837) : ℝ) /
        102400000000)

theorem corrC02701MinusMidpointZero2572 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def corrC02701MinusMidpointP000Center2572 : RatPair2542 := (0, 0)

def corrC02701MinusMidpointP000Factor2572 : RatPair2542 := (0, 0)

noncomputable def corrC02701MinusMidpointP000Error2572 : ℝ := 0

theorem corrC02701MinusMidpointP000Exterior2572 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02701MinusMidpointPosition2572 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |corrC02701MinusMidpointPosition2572| := by
    norm_num [storedWidth, corrC02701MinusMidpointPosition2572]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem corrC02701MinusMidpointP000BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP000Center2572‖ ≤
          corrC02701MinusMidpointP000Error2572 := by
  rw [corrC02701MinusMidpointP000Exterior2572]
  norm_num [corrC02701MinusMidpointP000Center2572, corrC02701MinusMidpointP000Error2572,
      corrC02701MinusMidpointZero2572]

theorem corrC02701MinusMidpointP000DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP000Factor2572 * embedPair2542
          corrC02701MinusMidpointP000Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP000Factor2572 : ℝ) *
            corrC02701MinusMidpointP000Error2572 := by
  rw [corrC02701MinusMidpointP000Exterior2572]
  norm_num [corrC02701MinusMidpointP000Factor2572, corrC02701MinusMidpointP000Center2572,
      corrC02701MinusMidpointP000Error2572,
      corrC02701MinusMidpointZero2572, pairMagnitude2542]

def corrC02701MinusMidpointP001Input2572 : RatPair2542 := ((((-((668 * 10^40
        + 8254807723076288264152476722223017963933) * 10^40
        + 5477557306256771509133844063953846090683)) : ℚ) /
        ((1887 * 10^40
        + 2004981127838775906823533063469056624951) * 10^40
        + 8551390361977395865728009214361600000000)),
    ((1751187200352461984105434273 : ℚ) /
        7378697629483820646400000000))

def corrC02701MinusMidpointP001Center2572 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP001Factor2572 : RatPair2542 :=
    ((((((((((7424858129877040379103063514147 * 10^40
        + 2046208360121633954182906132403570523864) * 10^40
        + 648428346274749511395136978418999184506) * 10^40
        + 9358507776888351933170707678365505632650) * 10^40
        + 8539161570714986782479944784049516523629) * 10^40
        + 6109523263199620455955379722991113432645) * 10^40
        + 8768336126887167364240352109784861288256) * 10^40
        + 9794740949661151786103643098547792528855) : ℚ) /
        (((((((20782228201096786123743073 * 10^40
        + 2525599440192868318545638888635957745059) * 10^40
        + 9405355048679421823974805922620803083835) * 10^40
        + 134384377627067432611882467793770205759) * 10^40
        + 2248084014968038169560658099908606349519) * 10^40
        + 5965338320913338551455551611648447457580) * 10^40
        + 1784933801424422902630966861891637528253) * 10^40
        + 8972691837633318734907394330777484263424)),
    (((-(((21561717659023772033175268292917794979 * 10^40
        + 9411270471589178068148274411273139315354) * 10^40
        + 6036907413841474235671484398408357135305) * 10^40
        + 1426556273480795037163279293975207987251)) : ℚ) /
        (((455875292169873866742237920983486 * 10^40
        + 6783956086599694778299636289552455319313) * 10^40
        + 140164076794329784882985441410357394279) * 10^40
        + 7962190625717799044169771443964103098368)))

noncomputable def corrC02701MinusMidpointP001Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP001BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP001Center2572‖ ≤
          corrC02701MinusMidpointP001Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP001Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP001Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP001Input2572 9 =
      (corrC02701MinusMidpointP001Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP001Input2572 9).2 : ℝ) =
      corrC02701MinusMidpointP001Error2572 := by
    rw [hs]
    norm_num [corrC02701MinusMidpointP001Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP001Input2572 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          corrC02701MinusMidpointP001Input2572)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP001Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP001DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP001Factor2572 * embedPair2542
          corrC02701MinusMidpointP001Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP001Factor2572 : ℝ) *
            corrC02701MinusMidpointP001Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP001Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP001Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP001BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP001Factor2572)

def corrC02701MinusMidpointP002Input2572 : RatPair2542 := ((((-((350 * 10^40
        + 6167159465445660897322667704655111564849) * 10^40
        + 7899260685951668685791997936374732229547)) : ℚ) /
        ((1497 * 10^40
        + 8141619820548260689071119881802050250108) * 10^40
        + 126749615182671161751511708467200000000)),
    (((-1751187200352461984105434273) : ℚ) /
        3689348814741910323200000000))

def corrC02701MinusMidpointP002Center2572 : RatPair2542 := ((((-7340606510045565236433) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-5832109500717769467319) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def corrC02701MinusMidpointP002Factor2572 : RatPair2542 :=
    ((((((((((11084611754380291585461843611 * 10^40
        + 4732930230937152997755471268433261187779) * 10^40
        + 7173817986211793147172705319797855131546) * 10^40
        + 1623116268348779277425115811623636597676) * 10^40
        + 2169914293228950451421458150897943440889) * 10^40
        + 7418115204053249089043795609343434395895) * 10^40
        + 5993939727759406388115038573650095963218) * 10^40
        + 5993583349558309156550614342199757781655) : ℚ) /
        (((((((131938533391840953334720621 * 10^40
        + 8825347156182027895959798474464112489693) * 10^40
        + 9671792158414417939027950473923060014877) * 10^40
        + 4289176939882047705810305489157946560841) * 10^40
        + 718066265242911267693960887873068942621) * 10^40
        + 1971332196028535473014904982177198305062) * 10^40
        + 433556986168407453096854955400435249183) * 10^40
        + 3338731144756634898574251359112280408064)),
    (((((3712192194107950273718682226584233483 * 10^40
        + 6986926611831851450849449243919379531256) * 10^40
        + 4227537839859281044320482299725491516319) * 10^40
        + 3520576290350883891989180506802913203731) : ℚ) /
        (((1148644999083010648418935679828095 * 10^40
        + 8725964118606440136677067135257354069503) * 10^40
        + 3424071534709150559522883614032650462252) * 10^40
        + 6050307411681401024348246517973681963008)))

noncomputable def corrC02701MinusMidpointP002Error2572 : ℝ := ((6359855276339487927 : ℝ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))

theorem corrC02701MinusMidpointP002BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP002Center2572‖ ≤
          corrC02701MinusMidpointP002Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP002Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP002Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP002Input2572 8 =
      (corrC02701MinusMidpointP002Center2572, ((6359855276339487927 : ℚ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP002Input2572 8).2 : ℝ) =
      corrC02701MinusMidpointP002Error2572 := by
    rw [hs]
    norm_num [corrC02701MinusMidpointP002Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP002Input2572 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          corrC02701MinusMidpointP002Input2572)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP002Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP002DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP002Factor2572 * embedPair2542
          corrC02701MinusMidpointP002Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP002Factor2572 : ℝ) *
            corrC02701MinusMidpointP002Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP002Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP002Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP002BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP002Factor2572)

def corrC02701MinusMidpointP003Input2572 : RatPair2542 := ((((-((45863 * 10^40
        + 2648834366119055615025041831922191898173) * 10^40
        + 965668249849210782996703504146014186969)) : ℚ) /
        ((271270 * 10^40
        + 3087127989071126638748716684898100330217) * 10^40
        + 4625034212383035136128999122534400000000)),
    (((-1751187200352461984105434273) : ℚ) /
        3689348814741910323200000000))

def corrC02701MinusMidpointP003Center2572 : RatPair2542 := ((((-124248799378105233681111054157) :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-197431261930242224312065802635) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def corrC02701MinusMidpointP003Factor2572 : RatPair2542 :=
    ((((-(((((((1742155612783365317703360079600024227819 *
    10^40
        + 1028445439867256700335882511417853201020) * 10^40
        + 5931325136594647591878314993421998454297) * 10^40
        + 4034448362051680805505256531436765560388) * 10^40
        + 7987676508569189373360285869934345615792) * 10^40
        + 1686372158571501453771021841093999337307) * 10^40
        + 1254464350390629391576555654863123361559) * 10^40
        + 7882409288560433376738036968116818862305)) : ℚ) /
        (((((((1277589923764623072860491930669287246 * 10^40
        + 5323592583042906058469514251362729734024) * 10^40
        + 7201655151557055716567626270175597351831) * 10^40
        + 1673047929909420137682320047349742412503) * 10^40
        + 7471100543210785281194830378611615594163) * 10^40
        + 1121952845627529378910118456416393472063) * 10^40
        + 4269302007342068507065934778311564815491) * 10^40
        + 8617433083633748807303403993846268297216)),
    ((((((12 * 10^40
        + 2600429882362719813830200873969423882383) * 10^40
        + 2953701898919978205607450493517992546410) * 10^40
        + 3234199498682267333321121731382962752376) * 10^40
        + 8949422336993123624403665088133379878897) : ℚ) /
        (((113030523477714774001326677076218828015 * 10^40
        + 3676547668716266699841468297573921341466) * 10^40
        + 8043997324608289989815148230992554401246) * 10^40
        + 1396662453661173234325213974407042564096)))

noncomputable def corrC02701MinusMidpointP003Error2572 : ℝ := ((806976511608363622744226945 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP003BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP003Center2572‖ ≤
          corrC02701MinusMidpointP003Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP003Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP003Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP003Input2572 8 =
      (corrC02701MinusMidpointP003Center2572, ((806976511608363622744226945 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP003Input2572 8).2 : ℝ) =
      corrC02701MinusMidpointP003Error2572 := by
    rw [hs]
    norm_num [corrC02701MinusMidpointP003Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP003Input2572 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          corrC02701MinusMidpointP003Input2572)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP003Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP003DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP003Factor2572 * embedPair2542
          corrC02701MinusMidpointP003Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP003Factor2572 : ℝ) *
            corrC02701MinusMidpointP003Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP003Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP003Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP003BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP003Factor2572)

def corrC02701MinusMidpointP004Input2572 : RatPair2542 := ((((-((38818 * 10^40
        + 9869011026983687992946176473055787532810) * 10^40
        + 4481020112683669260999281426307191747803)) : ℚ) /
        ((268088 * 10^40
        + 9931593660330219898315158741078364901345) * 10^40
        + 3125060162297126925824073714892800000000)),
    ((1751187200352461984105434273 : ℚ) /
        3689348814741910323200000000))

def corrC02701MinusMidpointP004Center2572 : RatPair2542 := ((((-15506492841082746575794339206295)
    : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((98559228420736481491679132241355 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def corrC02701MinusMidpointP004Factor2572 : RatPair2542 :=
    ((((-(((((((203293362852986614791537070876414578391 *
    10^40
        + 8859597003811590639994488269083882272313) * 10^40
        + 2970461141090546087937820535470353455949) * 10^40
        + 2880317493334144643199888914860132189826) * 10^40
        + 1957723491540831924835579487458149882581) * 10^40
        + 3703204192415455740366238054731634500718) * 10^40
        + 6763016596739658253249428909168342898321) * 10^40
        + 8723001761721023416142337240234307474345)) : ℚ) /
        (((((((135411595928757123875702755020406882 * 10^40
        + 7430206676041205504495923201060692890263) * 10^40
        + 9944180713238354832764943125854335799997) * 10^40
        + 9802366833398097661468701168259199408964) * 10^40
        + 9205313068610634292439206368383520502624) * 10^40
        + 3548336412481610697271534007440803450732) * 10^40
        + 4549188198565622983408235211953852997623) * 10^40
        + 1643313470550144096294061833208687755264)),
    (((-((((1 * 10^40
        + 9255662722924855656215274583036583190908) * 10^40
        + 5553142769192936695933280405106013384640) * 10^40
        + 6958977429308326775686595299915717690465) * 10^40
        + 5734346342275288089995499031060227158131)) : ℚ) /
        (((36798314625639735115744017436583249715 * 10^40
        + 1212116575041651561384933503454207921239) * 10^40
        + 8756483739036199863969920337379582093071) * 10^40
        + 3615121170672903486712689654810393182208)))

noncomputable def corrC02701MinusMidpointP004Error2572 : ℝ := ((98297418978311525453437400183 :
    ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem corrC02701MinusMidpointP004BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP004Center2572‖ ≤
          corrC02701MinusMidpointP004Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP004Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP004Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP004Input2572 8 =
      (corrC02701MinusMidpointP004Center2572, ((98297418978311525453437400183 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP004Input2572 8).2 : ℝ) =
      corrC02701MinusMidpointP004Error2572 := by
    rw [hs]
    norm_num [corrC02701MinusMidpointP004Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP004Input2572 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          corrC02701MinusMidpointP004Input2572)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP004Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP004DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP004Factor2572 * embedPair2542
          corrC02701MinusMidpointP004Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP004Factor2572 : ℝ) *
            corrC02701MinusMidpointP004Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP004Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP004Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP004BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP004Factor2572)

def corrC02701MinusMidpointP005Center2572 : RatPair2542 := (0, 0)

def corrC02701MinusMidpointP005Factor2572 : RatPair2542 := (0, 0)

noncomputable def corrC02701MinusMidpointP005Error2572 : ℝ := 0

theorem corrC02701MinusMidpointP005Exterior2572 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02701MinusMidpointPosition2572 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |corrC02701MinusMidpointPosition2572| := by
    norm_num [storedWidth, corrC02701MinusMidpointPosition2572]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem corrC02701MinusMidpointP005BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP005Center2572‖ ≤
          corrC02701MinusMidpointP005Error2572 := by
  rw [corrC02701MinusMidpointP005Exterior2572]
  norm_num [corrC02701MinusMidpointP005Center2572, corrC02701MinusMidpointP005Error2572,
      corrC02701MinusMidpointZero2572]

theorem corrC02701MinusMidpointP005DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP005Factor2572 * embedPair2542
          corrC02701MinusMidpointP005Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP005Factor2572 : ℝ) *
            corrC02701MinusMidpointP005Error2572 := by
  rw [corrC02701MinusMidpointP005Exterior2572]
  norm_num [corrC02701MinusMidpointP005Factor2572, corrC02701MinusMidpointP005Center2572,
      corrC02701MinusMidpointP005Error2572,
      corrC02701MinusMidpointZero2572, pairMagnitude2542]

def corrC02701MinusMidpointP006Input2572 : RatPair2542 :=
    ((((-336487691127537234939509440202342751) : ℚ) /
        587942314986765992027147468800000000),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP006Center2572 : RatPair2542 := (((11194442015994273 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP006Factor2572 : RatPair2542 := (((((453175520438156 * 10^40
        + 361769291046437722874375388159158900573) * 10^40
        + 8244520767183727720715763336846810476569) : ℚ) /
        ((91092303659 * 10^40
        + 3734186146287179594316829867022364143218) * 10^40
        + 2946903179357630882863053347387241906276)),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP006Error2572 : ℝ := ((7783662310233 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP006BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP006Center2572‖ ≤
          corrC02701MinusMidpointP006Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP006Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP006Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP006Input2572 7 =
      (corrC02701MinusMidpointP006Center2572, ((7783662310233 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP006Input2572 7).2 : ℝ) =
      corrC02701MinusMidpointP006Error2572 := by
    rw [hs]
    norm_num [corrC02701MinusMidpointP006Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP006Input2572 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          corrC02701MinusMidpointP006Input2572)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP006Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP006DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP006Factor2572 * embedPair2542
          corrC02701MinusMidpointP006Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP006Factor2572 : ℝ) *
            corrC02701MinusMidpointP006Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP006Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP006Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP006BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP006Factor2572)

def corrC02701MinusMidpointP007Input2572 : RatPair2542 := ((((-((45863 * 10^40
        + 2648834366119055615025041831922191898173) * 10^40
        + 965668249849210782996703504146014186969)) : ℚ) /
        ((67817 * 10^40
        + 5771781997267781659687179171224525082554) * 10^40
        + 3656258553095758784032249780633600000000)),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP007Center2572 : RatPair2542 := (((233274232040893355353989339387 : ℚ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP007Factor2572 : RatPair2542 := ((((((((((45700333870 * 10^40
        + 29611147336018885522740794693283050047) * 10^40
        + 1533152991779501720520892078610695609431) * 10^40
        + 7553123738014973534161481366756934880955) * 10^40
        + 3427968171715627661241266156698493633984) * 10^40
        + 1260870378617668115666909747046930333846) * 10^40
        + 3622440499351126843538865463203319293220) * 10^40
        + 5356702067722347600804545065601535683449) : ℚ) /
        (((((((258007230 * 10^40
        + 4031242290861211161553580853642871953942) * 10^40
        + 17085347620107399223438183325373725783) * 10^40
        + 8014599759851950543489692413636564878887) * 10^40
        + 8722658837265336781184268085360952162911) * 10^40
        + 6396645507960309336759777893881761399800) * 10^40
        + 4570394229397507350607064815239371617398) * 10^40
        + 5651320270889390403218180262406142733796)),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP007Error2572 : ℝ := ((16140561693539335055957957 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem corrC02701MinusMidpointP007BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP007Center2572‖ ≤
          corrC02701MinusMidpointP007Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP007Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP007Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP007Input2572 6 =
      (corrC02701MinusMidpointP007Center2572, ((16140561693539335055957957 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP007Input2572 6).2 : ℝ) =
      corrC02701MinusMidpointP007Error2572 := by
    rw [hs]
    norm_num [corrC02701MinusMidpointP007Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP007Input2572 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          corrC02701MinusMidpointP007Input2572)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP007Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP007DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP007Factor2572 * embedPair2542
          corrC02701MinusMidpointP007Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP007Factor2572 : ℝ) *
            corrC02701MinusMidpointP007Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP007Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP007Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP007BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP007Factor2572)

def corrC02701MinusMidpointP008Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1261197741322974723791937589 : ℚ) /
        944473296573929042739200000000))

def corrC02701MinusMidpointP008Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP008Factor2572 : RatPair2542 := (((((((((((66232 * 10^40
        + 9144464737951886725007940595601611487104) * 10^40
        + 9616599659405284289197994788378392607877) * 10^40
        + 1407641071147865284837020511239686572607) * 10^40
        + 4300025139402278386106045599964143736372) * 10^40
        + 9124155565704412297524347893665342149227) * 10^40
        + 8353532266241407498558918999727799864015) * 10^40
        + 6585705038934440712259249210761576622683) * 10^40
        + 9364780035755840122245254642964337958375) : ℚ) /
        (((((((4169066886545017168806093577099 * 10^40
        + 2804841626764728485775059918649364161105) * 10^40
        + 7156297582235054199635008787006296965286) * 10^40
        + 684020108796962676512317814233549069182) * 10^40
        + 956436925361386995735136373577472584497) * 10^40
        + 8294342970545963682423715151865053193691) * 10^40
        + 7217764807399723230526878725170332382082) * 10^40
        + 9463760507013221333253475845304236376064)),
    (((-((((7275 * 10^40
        + 6574349916634787016998195373904049234561) * 10^40
        + 8065007495913711292902109148985149580917) * 10^40
        + 9332917144256181967964859840562926167946) * 10^40
        + 8526295545076079776497288842256015375621)) : ℚ) /
        (((204182929907106024189758774225541583 * 10^40
        + 8214588488908717377422432983680743599465) * 10^40
        + 4242336465525581924812698515115500599032) * 10^40
        + 9199626782652513119530945102618392788992)))

noncomputable def corrC02701MinusMidpointP008Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP008BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP008Center2572‖ ≤
          corrC02701MinusMidpointP008Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP008Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP008Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP008Input2572 15 =
      (corrC02701MinusMidpointP008Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP008Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP008Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP008Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP008Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP008Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP008Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP008DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP008Factor2572 * embedPair2542
          corrC02701MinusMidpointP008Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP008Factor2572 : ℝ) *
            corrC02701MinusMidpointP008Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP008Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP008Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP008BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP008Factor2572)

def corrC02701MinusMidpointP009Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1875731480065194149050312107 : ℚ) /
        944473296573929042739200000000))

def corrC02701MinusMidpointP009Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP009Factor2572 : RatPair2542 := (((((((((((66232 * 10^40
        + 9144463728471975557765285225272421479677) * 10^40
        + 9091674004691249176757495600306899280329) * 10^40
        + 2166993897099392249394692428378149156755) * 10^40
        + 5072022317083615439231317494255178454752) * 10^40
        + 23970219643669379245198220545014553244) * 10^40
        + 2473439986190354319094991562056436085669) * 10^40
        + 1616425182370169619374327267844539599718) * 10^40
        + 3652601781223138769140895108306010398887) : ℚ) /
        (((((((4169066886545017168806093577099 * 10^40
        + 2804841626764728485775059918649364161105) * 10^40
        + 7156297582235054199635008787006296965286) * 10^40
        + 684020108796962676512317814233549069182) * 10^40
        + 956436925361386995735136373577472584497) * 10^40
        + 8294342970545963682423715151865053193691) * 10^40
        + 7217764807399723230526878725170332382082) * 10^40
        + 9463760507013221333253475845304236376064)),
    (((-((((3606 * 10^40
        + 9362854679685708435212403848183270104690) * 10^40
        + 5647277403384666135826345512951625455713) * 10^40
        + 8091353176784035430861672880758964338478) * 10^40
        + 6369370071776261590468561710231603860041)) : ℚ) /
        (((68060976635702008063252924741847194 * 10^40
        + 6071529496302905792474144327893581199821) * 10^40
        + 8080778821841860641604232838371833533010) * 10^40
        + 9733208927550837706510315034206130929664)))

noncomputable def corrC02701MinusMidpointP009Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP009BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP009Center2572‖ ≤
          corrC02701MinusMidpointP009Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP009Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP009Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP009Input2572 15 =
      (corrC02701MinusMidpointP009Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP009Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP009Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP009Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP009Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP009Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP009Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP009DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP009Factor2572 * embedPair2542
          corrC02701MinusMidpointP009Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP009Factor2572 : ℝ) *
            corrC02701MinusMidpointP009Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP009Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP009Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP009BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP009Factor2572)

def corrC02701MinusMidpointP010Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1115820674697574220099746077 : ℚ) /
        472236648286964521369600000000))

def corrC02701MinusMidpointP010Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP010Factor2572 : RatPair2542 := (((((((((((16558 * 10^40
        + 2286115740740265438047936396715653839565) * 10^40
        + 7705448476164123481891125537032655171806) * 10^40
        + 5143748294346683993127864099808803793282) * 10^40
        + 7045894791180135055190775322564952538598) * 10^40
        + 8312256411595120066310191079278456270085) * 10^40
        + 5085714438028603067408382381738067479765) * 10^40
        + 342130701482244285482969261807371468035) * 10^40
        + 8666483353430438333105457989156452774295) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((2145 * 10^40
        + 6664359560388488955028471120819908198412) * 10^40
        + 7732278299928707093278580807739096292025) * 10^40
        + 9369259228453726194625291685016169817503) * 10^40
        + 4868076817275282135160165891749886483151)) : ℚ) /
        (((34030488317851004031626462370923597 * 10^40
        + 3035764748151452896237072163946790599910) * 10^40
        + 9040389410920930320802116419185916766505) * 10^40
        + 4866604463775418853255157517103065464832)))

noncomputable def corrC02701MinusMidpointP010Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP010BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP010Center2572‖ ≤
          corrC02701MinusMidpointP010Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP010Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP010Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP010Input2572 15 =
      (corrC02701MinusMidpointP010Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP010Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP010Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP010Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP010Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP010Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP010Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP010DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP010Factor2572 * embedPair2542
          corrC02701MinusMidpointP010Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP010Factor2572 : ℝ) *
            corrC02701MinusMidpointP010Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP010Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP010Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP010BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP010Factor2572)

def corrC02701MinusMidpointP011Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1234468557765072383258963437 : ℚ) /
        472236648286964521369600000000))

def corrC02701MinusMidpointP011Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP011Factor2572 : RatPair2542 := (((((((((((16558 * 10^40
        + 2286115594714821718566984399754228157923) * 10^40
        + 8279713808393667747621063476224768957195) * 10^40
        + 7798176737254397187269708972643524351755) * 10^40
        + 8474072655622984058156416423164838029877) * 10^40
        + 6288475740198007226228077253623067908927) * 10^40
        + 9064329293443689823317150717455986278617) * 10^40
        + 7186200892030108593977711678670640920193) * 10^40
        + 9262349211738484647502306164630318455) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((7121 * 10^40
        + 4608512899586962603711870439476617718525) * 10^40
        + 5954698190410201596228194338447775968058) * 10^40
        + 5122026761578764451565647555284869254130) * 10^40
        + 2361633372442723579012180724540565842493)) : ℚ) /
        (((102091464953553012094879387112770791 * 10^40
        + 9107294244454358688711216491840371799732) * 10^40
        + 7121168232762790962406349257557750299516) * 10^40
        + 4599813391326256559765472551309196394496)))

noncomputable def corrC02701MinusMidpointP011Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP011BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP011Center2572‖ ≤
          corrC02701MinusMidpointP011Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP011Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP011Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP011Input2572 15 =
      (corrC02701MinusMidpointP011Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP011Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP011Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP011Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP011Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP011Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP011Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP011DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP011Factor2572 * embedPair2542
          corrC02701MinusMidpointP011Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP011Factor2572 : ℝ) *
            corrC02701MinusMidpointP011Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP011Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP011Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP011BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP011Factor2572)

def corrC02701MinusMidpointP012Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((27147174540145397472943033 : ℚ) /
        9444732965739290427392000000))

def corrC02701MinusMidpointP012Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP012Factor2572 : RatPair2542 := (((((((((((4139 * 10^40
        + 5571528856981165018436493861088751897503) * 10^40
        + 7381892663200576481415739175252665294561) * 10^40
        + 1042622583169640596359518722750044089774) * 10^40
        + 3851072832918091149200270849536208388133) * 10^40
        + 1269154724741392887702430421477701745109) * 10^40
        + 1062539171842012285707022172533277044243) * 10^40
        + 3859225932146628164809705891509910562511) * 10^40
        + 3283162392712186364296959731514528962751) : ℚ) /
        (((((((260566680409063573050380848568 * 10^40
        + 7050302601672795530360941244915585260069) * 10^40
        + 1072268598889690887477188049187893560330) * 10^40
        + 3792751256799810167282019863389596816823) * 10^40
        + 8809777307835086687233446023348592036531) * 10^40
        + 1143396435659122730151482196991565824605) * 10^40
        + 7326110300462482701907929920323145773880) * 10^40
        + 1841485031688326333328342240331514773504)),
    (((-((((3915 * 10^40
        + 1977483490603883771039200416796270564901) * 10^40
        + 8536176746320455053303262455936960081675) * 10^40
        + 6694772882332347979075600734791421820434) * 10^40
        + 3056140791758253455809680744316189483425)) : ℚ) /
        (((51045732476776506047439693556385395 * 10^40
        + 9553647122227179344355608245920185899866) * 10^40
        + 3560584116381395481203174628778875149758) * 10^40
        + 2299906695663128279882736275654598197248)))

noncomputable def corrC02701MinusMidpointP012Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP012BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP012Center2572‖ ≤
          corrC02701MinusMidpointP012Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP012Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP012Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP012Input2572 15 =
      (corrC02701MinusMidpointP012Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP012Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP012Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP012Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP012Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP012Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP012Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP012DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP012Factor2572 * embedPair2542
          corrC02701MinusMidpointP012Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP012Factor2572 : ℝ) *
            corrC02701MinusMidpointP012Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP012Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP012Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP012BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP012Factor2572)

def corrC02701MinusMidpointP013Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((293869352734311453179388567 : ℚ) /
        94447329657392904273920000000))

def corrC02701MinusMidpointP013Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP013Factor2572 : RatPair2542 := (((((((((((16558 * 10^40
        + 2286115262157146595349617900512894893477) * 10^40
        + 827825164453322201228792067879036269315) * 10^40
        + 3583248563899612346281621047021510451671) * 10^40
        + 4989184302684719594993947522658143907165) * 10^40
        + 4878693057518332410845344324834221170337) * 10^40
        + 9812003907510014255428273746749134879669) * 10^40
        + 2226784903797893208971930266989901002418) * 10^40
        + 8415540231515546945392887656773628724279) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((2825 * 10^40
        + 4791339524051289529821841961168704463883) * 10^40
        + 4716831223198120003212322654893117349803) * 10^40
        + 8440955790008132007638251150364424143036) * 10^40
        + 7196955532250531644790525611354991355105)) : ℚ) /
        (((34030488317851004031626462370923597 * 10^40
        + 3035764748151452896237072163946790599910) * 10^40
        + 9040389410920930320802116419185916766505) * 10^40
        + 4866604463775418853255157517103065464832)))

noncomputable def corrC02701MinusMidpointP013Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP013BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP013Center2572‖ ≤
          corrC02701MinusMidpointP013Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP013Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP013Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP013Input2572 15 =
      (corrC02701MinusMidpointP013Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP013Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP013Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP013Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP013Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP013Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP013Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP013DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP013Factor2572 * embedPair2542
          corrC02701MinusMidpointP013Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP013Factor2572 : ℝ) *
            corrC02701MinusMidpointP013Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP013Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP013Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP013BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP013Factor2572)

def corrC02701MinusMidpointP014Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1676849125948274871802318207 : ℚ) /
        472236648286964521369600000000))

def corrC02701MinusMidpointP014Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP014Factor2572 : RatPair2542 := (((((((((((16558 * 10^40
        + 2286114920291049145680661729293004561737) * 10^40
        + 852914172016988464305996673176887798213) * 10^40
        + 1795928763989343937061803904127319938830) * 10^40
        + 3030218123428738113511259411857235903744) * 10^40
        + 4996564669902195739095866386158494066058) * 10^40
        + 3765647736326128205256310029131867327500) * 10^40
        + 7413391242457066278666925015175158496314) * 10^40
        + 2087295000006890266814581478659297034975) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((9673 * 10^40
        + 4868853848879936168468354199761778736006) * 10^40
        + 9028835208754915510917900007065181098145) * 10^40
        + 511962627329779523631453975334684816558) * 10^40
        + 2301001285159187984736590317917774103023)) : ℚ) /
        (((102091464953553012094879387112770791 * 10^40
        + 9107294244454358688711216491840371799732) * 10^40
        + 7121168232762790962406349257557750299516) * 10^40
        + 4599813391326256559765472551309196394496)))

noncomputable def corrC02701MinusMidpointP014Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP014BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP014Center2572‖ ≤
          corrC02701MinusMidpointP014Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP014Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP014Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP014Input2572 15 =
      (corrC02701MinusMidpointP014Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP014Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP014Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP014Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP014Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP014Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP014Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP014DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP014Factor2572 * embedPair2542
          corrC02701MinusMidpointP014Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP014Factor2572 : ℝ) *
            corrC02701MinusMidpointP014Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP014Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP014Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP014BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP014Factor2572)

def corrC02701MinusMidpointP015Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1825525274756649096408550339 : ℚ) /
        472236648286964521369600000000))

def corrC02701MinusMidpointP015Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP015Factor2572 : RatPair2542 := (((((((((((16558 * 10^40
        + 2286114647612419581521351770133549041199) * 10^40
        + 7650006102676757482102001624331821265458) * 10^40
        + 4365114698828630978410603095177004777149) * 10^40
        + 5564389528838839844430660572791111080968) * 10^40
        + 691957275003837432006850127381456185204) * 10^40
        + 8119654832542814632365540534723413269661) * 10^40
        + 6048852025058134317979889016413805927787) * 10^40
        + 6325298238115989003523660992441629515863) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((10531 * 10^40
        + 1769145066279725206860098876104106622206) * 10^40
        + 9741948340786440614484208038926015611060) * 10^40
        + 88491061190001039318216889148190448873) * 10^40
        + 9483120426119825570157652810681779360371)) : ℚ) /
        (((102091464953553012094879387112770791 * 10^40
        + 9107294244454358688711216491840371799732) * 10^40
        + 7121168232762790962406349257557750299516) * 10^40
        + 4599813391326256559765472551309196394496)))

noncomputable def corrC02701MinusMidpointP015Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP015BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP015Center2572‖ ≤
          corrC02701MinusMidpointP015Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP015Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP015Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP015Input2572 15 =
      (corrC02701MinusMidpointP015Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP015Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP015Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP015Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP015Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP015Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP015Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP015DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP015Factor2572 * embedPair2542
          corrC02701MinusMidpointP015Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP015Factor2572 : ℝ) *
            corrC02701MinusMidpointP015Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP015Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP015Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP015BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP015Factor2572)

def corrC02701MinusMidpointP016Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((966485135227022568073460733 : ℚ) /
        236118324143482260684800000000))

def corrC02701MinusMidpointP016Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP016Factor2572 : RatPair2542 := (((((((((((4139 * 10^40
        + 5571528609035763494199380878028336993477) * 10^40
        + 1242052320502771864030590690113998594065) * 10^40
        + 6368522415381834555582579335283534443805) * 10^40
        + 5719960865088380233671527306080161666931) * 10^40
        + 3541273245183934258226357284438301451892) * 10^40
        + 8985119903288013052305805813122774773573) * 10^40
        + 1569545266368571196788041951864829083778) * 10^40
        + 334955931510289309861350467241363451607) : ℚ) /
        (((((((260566680409063573050380848568 * 10^40
        + 7050302601672795530360941244915585260069) * 10^40
        + 1072268598889690887477188049187893560330) * 10^40
        + 3792751256799810167282019863389596816823) * 10^40
        + 8809777307835086687233446023348592036531) * 10^40
        + 1143396435659122730151482196991565824605) * 10^40
        + 7326110300462482701907929920323145773880) * 10^40
        + 1841485031688326333328342240331514773504)),
    (((-((((109 * 10^40
        + 3236344034200033289674123990541373560649) * 10^40
        + 1744178475117676398831194807686683035082) * 10^40
        + 7552884254446568110072992252577754124241) * 10^40
        + 9442050552183456123878097533174161500287)) : ℚ) /
        (((1000896715230911883283131246203635 * 10^40
        + 2148110727886807438124619769527846782350) * 10^40
        + 3207070276791792068258885777034879904897) * 10^40
        + 2201958954816924083919269338738325454848)))

noncomputable def corrC02701MinusMidpointP016Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP016BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP016Center2572‖ ≤
          corrC02701MinusMidpointP016Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP016Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP016Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP016Input2572 15 =
      (corrC02701MinusMidpointP016Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP016Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP016Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP016Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP016Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP016Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP016Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP016DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP016Factor2572 * embedPair2542
          corrC02701MinusMidpointP016Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP016Factor2572 : ℝ) *
            corrC02701MinusMidpointP016Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP016Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP016Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP016BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP016Factor2572)

def corrC02701MinusMidpointP017Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((2141675457290368202103352599 : ℚ) /
        472236648286964521369600000000))

def corrC02701MinusMidpointP017Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP017Factor2572 : RatPair2542 := (((((((((((16558 * 10^40
        + 2286113990824974916057599500746115042200) * 10^40
        + 9133703275499335202614563633128512573251) * 10^40
        + 5106393448443488807654847372729041461835) * 10^40
        + 3857240891667327148080399933453251208134) * 10^40
        + 337451824320897234345014992550180056633) * 10^40
        + 2580205213932680244503274435679327480445) * 10^40
        + 86964327131974238199667182627404718014) * 10^40
        + 5537306703150386391567987474724766674383) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((4118 * 10^40
        + 3330347093937104643282056905170738168590) * 10^40
        + 4752025604164890771254680913102309305459) * 10^40
        + 4628990423405097298945751307188061817758) * 10^40
        + 6826653522595864828234373866366704209837)) : ℚ) /
        (((34030488317851004031626462370923597 * 10^40
        + 3035764748151452896237072163946790599910) * 10^40
        + 9040389410920930320802116419185916766505) * 10^40
        + 4866604463775418853255157517103065464832)))

noncomputable def corrC02701MinusMidpointP017Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP017BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP017Center2572‖ ≤
          corrC02701MinusMidpointP017Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP017Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP017Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP017Input2572 15 =
      (corrC02701MinusMidpointP017Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP017Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP017Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP017Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP017Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP017Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP017Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP017DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP017Factor2572 * embedPair2542
          corrC02701MinusMidpointP017Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP017Factor2572 : ℝ) *
            corrC02701MinusMidpointP017Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP017Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP017Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP017BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP017Factor2572)

def corrC02701MinusMidpointP018Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((555145611856273095972878081 : ℚ) /
        118059162071741130342400000000))

def corrC02701MinusMidpointP018Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP018Factor2572 : RatPair2542 := (((((((((((1034 * 10^40
        + 8892882113160967775114780229092201353440) * 10^40
        + 6129531859141386544497610409182746651991) * 10^40
        + 5270461817706738127127038189264573462041) * 10^40
        + 8445472998585077717444296271629792142668) * 10^40
        + 5288946690856845542138610795156309111335) * 10^40
        + 1796182847442402358408177993834584562005) * 10^40
        + 839736745428434453277648675594916945535) * 10^40
        + 3024216499818478015620019439358543223263) : ℚ) /
        (((((((65141670102265893262595212142 * 10^40
        + 1762575650418198882590235311228896315017) * 10^40
        + 2768067149722422721869297012296973390082) * 10^40
        + 5948187814199952541820504965847399204205) * 10^40
        + 9702444326958771671808361505837148009132) * 10^40
        + 7785849108914780682537870549247891456151) * 10^40
        + 4331527575115620675476982480080786443470) * 10^40
        + 460371257922081583332085560082878693376)),
    (((-((((3202 * 10^40
        + 5503741928655233405894195647743315168631) * 10^40
        + 8371482090781678037565361404575145672418) * 10^40
        + 1768746182755019901970219040794175999075) * 10^40
        + 2215099972656398572945722884690919525009)) : ℚ) /
        (((25522866238388253023719846778192697 * 10^40
        + 9776823561113589672177804122960092949933) * 10^40
        + 1780292058190697740601587314389437574879) * 10^40
        + 1149953347831564139941368137827299098624)))

noncomputable def corrC02701MinusMidpointP018Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP018BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP018Center2572‖ ≤
          corrC02701MinusMidpointP018Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP018Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP018Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP018Input2572 15 =
      (corrC02701MinusMidpointP018Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP018Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP018Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP018Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP018Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP018Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP018Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP018DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP018Factor2572 * embedPair2542
          corrC02701MinusMidpointP018Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP018Factor2572 : ℝ) *
            corrC02701MinusMidpointP018Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP018Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP018Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP018BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP018Factor2572)

def corrC02701MinusMidpointP019Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((118159442675668676717562267 : ℚ) /
        23611832414348226068480000000))

def corrC02701MinusMidpointP019Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP019Factor2572 : RatPair2542 := (((((((((((1034 * 10^40
        + 8892882091767104135178518670326176012219) * 10^40
        + 4268738291779388012517595574556984223090) * 10^40
        + 4867033658844013187601759859131970599966) * 10^40
        + 5062888399097842676733415248840776523965) * 10^40
        + 9580212209496267320000990478876030910764) * 10^40
        + 1859108307156339108700305721517204588125) * 10^40
        + 8618917725444547769390673393375289639296) * 10^40
        + 2884294304635593273685285825893950579119) : ℚ) /
        (((((((65141670102265893262595212142 * 10^40
        + 1762575650418198882590235311228896315017) * 10^40
        + 2768067149722422721869297012296973390082) * 10^40
        + 5948187814199952541820504965847399204205) * 10^40
        + 9702444326958771671808361505837148009132) * 10^40
        + 7785849108914780682537870549247891456151) * 10^40
        + 4331527575115620675476982480080786443470) * 10^40
        + 460371257922081583332085560082878693376)),
    (((-((((1136 * 10^40
        + 730088155493333122451753302052452560190) * 10^40
        + 3095884605448331242796794821829512751999) * 10^40
        + 868361811027192765808159558104301309693) * 10^40
        + 6335641740181808632787195831736493220605)) : ℚ) /
        (((8507622079462751007906615592730899 * 10^40
        + 3258941187037863224059268040986697649977) * 10^40
        + 7260097352730232580200529104796479191626) * 10^40
        + 3716651115943854713313789379275766366208)))

noncomputable def corrC02701MinusMidpointP019Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP019BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP019Center2572‖ ≤
          corrC02701MinusMidpointP019Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP019Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP019Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP019Input2572 15 =
      (corrC02701MinusMidpointP019Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP019Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP019Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP019Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP019Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP019Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP019Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP019DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP019Factor2572 * embedPair2542
          corrC02701MinusMidpointP019Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP019Factor2572 : ℝ) *
            corrC02701MinusMidpointP019Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP019Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP019Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP019BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP019Factor2572)

def corrC02701MinusMidpointP020Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((2518261918355091626130213703 : ℚ) /
        472236648286964521369600000000))

def corrC02701MinusMidpointP020Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP020Factor2572 : RatPair2542 := (((((((((((16558 * 10^40
        + 2286113071874699210073320164636828126330) * 10^40
        + 1519595992151446095064709243592222157299) * 10^40
        + 7682640238100638629876714948018345659374) * 10^40
        + 4135560823634200281983962920840409927006) * 10^40
        + 6721442199358800942627788454776438918292) * 10^40
        + 2049228555748328969763804198273677161475) * 10^40
        + 6894279587717832300464493681389117326065) * 10^40
        + 3747541585591805879853505618094168122415) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((14527 * 10^40
        + 4689679646250954703737469702745973777388) * 10^40
        + 5199476345584757607918880778110177084973) * 10^40
        + 6722582937044863061950075873452875178081) * 10^40
        + 2356110868273434610683238130663079974967)) : ℚ) /
        (((102091464953553012094879387112770791 * 10^40
        + 9107294244454358688711216491840371799732) * 10^40
        + 7121168232762790962406349257557750299516) * 10^40
        + 4599813391326256559765472551309196394496)))

noncomputable def corrC02701MinusMidpointP020Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP020BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP020Center2572‖ ≤
          corrC02701MinusMidpointP020Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP020Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP020Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP020Input2572 15 =
      (corrC02701MinusMidpointP020Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP020Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP020Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP020Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP020Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP020Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP020Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP020DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP020Factor2572 * embedPair2542
          corrC02701MinusMidpointP020Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP020Factor2572 : ℝ) *
            corrC02701MinusMidpointP020Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP020Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP020Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP020BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP020Factor2572)

def corrC02701MinusMidpointP021Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((2647676452840152643307498919 : ℚ) /
        472236648286964521369600000000))

def corrC02701MinusMidpointP021Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP021Factor2572 : RatPair2542 := (((((((((((16558 * 10^40
        + 2286112721784860960582705973988022498918) * 10^40
        + 6808672600066066608839552166416994208017) * 10^40
        + 7750704475035250847623361570419368987552) * 10^40
        + 7235511997185317764952502559577441107818) * 10^40
        + 5469129862408896129738898448125514213006) * 10^40
        + 9348289705357516686116512953864922463397) * 10^40
        + 9536345852387574967263433107582814112220) * 10^40
        + 516026536494259808358919173065938077423) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((5091 * 10^40
        + 3472271608626996982061227481078589997744) * 10^40
        + 1600474520674587305460658911444098824045) * 10^40
        + 5322710538674404036798683731027337490913) * 10^40
        + 8148231437446459883980873057065940875997)) : ℚ) /
        (((34030488317851004031626462370923597 * 10^40
        + 3035764748151452896237072163946790599910) * 10^40
        + 9040389410920930320802116419185916766505) * 10^40
        + 4866604463775418853255157517103065464832)))

noncomputable def corrC02701MinusMidpointP021Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP021BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP021Center2572‖ ≤
          corrC02701MinusMidpointP021Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP021Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP021Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP021Input2572 15 =
      (corrC02701MinusMidpointP021Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP021Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP021Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP021Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP021Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP021Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP021Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP021DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP021Factor2572 * embedPair2542
          corrC02701MinusMidpointP021Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP021Factor2572 : ℝ) *
            corrC02701MinusMidpointP021Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP021Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP021Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP021BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP021Factor2572)

def corrC02701MinusMidpointP022Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((542783116803371403996659021 : ℚ) /
        94447329657392904273920000000))

def corrC02701MinusMidpointP022Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP022Factor2572 : RatPair2542 := (((((((((((16558 * 10^40
        + 2286112535809409067978823240397311119230) * 10^40
        + 6708017829761092806751340295181713286280) * 10^40
        + 6430079329744398950391664165002363653369) * 10^40
        + 3932508826962927439239106729449449809288) * 10^40
        + 547316294187594170798406175989064924214) * 10^40
        + 4313197307168355375125704050946203129039) * 10^40
        + 7696733992776234593932368751769832911597) * 10^40
        + 7641521204708288609211984092381479584479) : ℚ) /
        (((((((1042266721636254292201523394274 * 10^40
        + 8201210406691182121443764979662341040276) * 10^40
        + 4289074395558763549908752196751574241321) * 10^40
        + 5171005027199240669128079453558387267295) * 10^40
        + 5239109231340346748933784093394368146124) * 10^40
        + 4573585742636490920605928787966263298422) * 10^40
        + 9304441201849930807631719681292583095520) * 10^40
        + 7365940126753305333313368961326059094016)),
    (((-((((15656 * 10^40
        + 1651276660847745338137854937834203600721) * 10^40
        + 4679301629680753071876761757862249312143) * 10^40
        + 752686681230875594747084303119849395500) * 10^40
        + 5077537152578514576783766945696829603345)) : ℚ) /
        (((102091464953553012094879387112770791 * 10^40
        + 9107294244454358688711216491840371799732) * 10^40
        + 7121168232762790962406349257557750299516) * 10^40
        + 4599813391326256559765472551309196394496)))

noncomputable def corrC02701MinusMidpointP022Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP022BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP022Center2572‖ ≤
          corrC02701MinusMidpointP022Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP022Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP022Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP022Input2572 15 =
      (corrC02701MinusMidpointP022Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP022Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP022Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP022Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP022Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP022Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP022Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP022DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP022Factor2572 * embedPair2542
          corrC02701MinusMidpointP022Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP022Factor2572 : ℝ) *
            corrC02701MinusMidpointP022Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP022Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP022Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP022BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP022Factor2572)

def corrC02701MinusMidpointP023Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1452447653947712451580278721 : ℚ) /
        236118324143482260684800000000))

def corrC02701MinusMidpointP023Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP023Factor2572 : RatPair2542 := (((((((((((4139 * 10^40
        + 5571527993470923634033121499469862422216) * 10^40
        + 1495733712038161180557213121403975921680) * 10^40
        + 8992294707051131120401375287324101020795) * 10^40
        + 6445608702324552069488265528359989304832) * 10^40
        + 8094623372311565008955852216997524396091) * 10^40
        + 9767070982401550569485975252290973657717) * 10^40
        + 4806741168738564944460239669045126047824) * 10^40
        + 1007395697875017398242989250759183800415) : ℚ) /
        (((((((260566680409063573050380848568 * 10^40
        + 7050302601672795530360941244915585260069) * 10^40
        + 1072268598889690887477188049187893560330) * 10^40
        + 3792751256799810167282019863389596816823) * 10^40
        + 8809777307835086687233446023348592036531) * 10^40
        + 1143396435659122730151482196991565824605) * 10^40
        + 7326110300462482701907929920323145773880) * 10^40
        + 1841485031688326333328342240331514773504)),
    (((-((((8378 * 10^40
        + 9490150019893628982769487458714385244637) * 10^40
        + 9266024391490518048922772595174383374809) * 10^40
        + 4194841072813433372020957838743891471907) * 10^40
        + 2251539575224661652620387152479894533969)) : ℚ) /
        (((51045732476776506047439693556385395 * 10^40
        + 9553647122227179344355608245920185899866) * 10^40
        + 3560584116381395481203174628778875149758) * 10^40
        + 2299906695663128279882736275654598197248)))

noncomputable def corrC02701MinusMidpointP023Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP023BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP023Center2572‖ ≤
          corrC02701MinusMidpointP023Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP023Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP023Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP023Input2572 15 =
      (corrC02701MinusMidpointP023Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP023Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP023Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP023Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP023Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP023Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP023Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP023DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP023Factor2572 * embedPair2542
          corrC02701MinusMidpointP023Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP023Factor2572 : ℝ) *
            corrC02701MinusMidpointP023Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP023Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP023Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP023BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP023Factor2572)

def corrC02701MinusMidpointP024Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1496330927553297167442947039 : ℚ) /
        236118324143482260684800000000))

def corrC02701MinusMidpointP024Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP024Factor2572 : RatPair2542 := (((((((((((4139 * 10^40
        + 5571527925708581146076034624302343020751) * 10^40
        + 1033415546468853405639187995457698498067) * 10^40
        + 9677933760151147434429256217486423611342) * 10^40
        + 9524084976075738283818708496867517920731) * 10^40
        + 7654465456213542839078018874827453692347) * 10^40
        + 507076825544653725857503336931724612043) * 10^40
        + 1788622044972060956421656109637637129366) * 10^40
        + 2614776007690528446717246526120057951135) : ℚ) /
        (((((((260566680409063573050380848568 * 10^40
        + 7050302601672795530360941244915585260069) * 10^40
        + 1072268598889690887477188049187893560330) * 10^40
        + 3792751256799810167282019863389596816823) * 10^40
        + 8809777307835086687233446023348592036531) * 10^40
        + 1143396435659122730151482196991565824605) * 10^40
        + 7326110300462482701907929920323145773880) * 10^40
        + 1841485031688326333328342240331514773504)),
    (((-((((8632 * 10^40
        + 1049281622262242124060050967649267576803) * 10^40
        + 6901592252326561343013612933462787534232) * 10^40
        + 9398689619484209462244211589569199377920) * 10^40
        + 6020829934517731440015979444180935726671)) : ℚ) /
        (((51045732476776506047439693556385395 * 10^40
        + 9553647122227179344355608245920185899866) * 10^40
        + 3560584116381395481203174628778875149758) * 10^40
        + 2299906695663128279882736275654598197248)))

noncomputable def corrC02701MinusMidpointP024Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP024BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP024Center2572‖ ≤
          corrC02701MinusMidpointP024Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP024Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP024Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP024Input2572 15 =
      (corrC02701MinusMidpointP024Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP024Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP024Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP024Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP024Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP024Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP024Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP024DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP024Factor2572 * embedPair2542
          corrC02701MinusMidpointP024Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP024Factor2572 : ℝ) *
            corrC02701MinusMidpointP024Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP024Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP024Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP024BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP024Factor2572)

def corrC02701MinusMidpointP025Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((48479765632462230989059221 : ℚ) /
        7378697629483820646400000000))

def corrC02701MinusMidpointP025Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP025Factor2572 : RatPair2542 := (((((((((((4 * 10^40
        + 425362820154196627537037709924783443162) * 10^40
        + 1807777075197067944010242260049936154504) * 10^40
        + 2927611509709727699628221088077747431035) * 10^40
        + 8546010894720941802837546765660298318045) * 10^40
        + 2335565874251575038640278609633461306315) * 10^40
        + 6032525171535322779257159762434888989945) * 10^40
        + 7836752538779987545247621654241239227764) * 10^40
        + 4680134667165989738622517888079611892263) : ℚ) /
        (((((((254459648836976145557012547 * 10^40
        + 4303760061134446089385118106684487876230) * 10^40
        + 5362375262303603213757301941454285052305) * 10^40
        + 101360108649218564616486347522841403141) * 10^40
        + 4295712673152182701843001412132176359410) * 10^40
        + 6749163473081698362041163556832999576000) * 10^40
        + 5915357529590295393263581962812815572044) * 10^40
        + 8048673325226258131184890959219073744896)),
    (((-((((93 * 10^40
        + 2241248969353193297825534681590694696250) * 10^40
        + 2506377785830354550351070837755475367661) * 10^40
        + 3683137942954163416703629239827627232408) * 10^40
        + 4742378598649500476965954000655898632823)) : ℚ) /
        (((531726379966421937994163474545681 * 10^40
        + 2078683824189866451503704252561668603123) * 10^40
        + 6078756084545639536262533069049779949476) * 10^40
        + 6482290694746490919582111836204735397888)))

noncomputable def corrC02701MinusMidpointP025Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP025BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP025Center2572‖ ≤
          corrC02701MinusMidpointP025Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP025Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP025Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP025Input2572 15 =
      (corrC02701MinusMidpointP025Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP025Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP025Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP025Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP025Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP025Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP025Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP025DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP025Factor2572 * embedPair2542
          corrC02701MinusMidpointP025Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP025Factor2572 : ℝ) *
            corrC02701MinusMidpointP025Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP025Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP025Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP025BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP025Factor2572)

def corrC02701MinusMidpointP026Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((100473894490366930888172769 : ℚ) /
        14757395258967641292800000000))

def corrC02701MinusMidpointP026Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP026Factor2572 : RatPair2542 := (((((((((((16 * 10^40
        + 1701451280253445384943055350345939162479) * 10^40
        + 3861381635772908002659701698996876320077) * 10^40
        + 8872878590364129462331885248059517852747) * 10^40
        + 2851166216529947910216787783709046427074) * 10^40
        + 7655243154885890882187317115519002793845) * 10^40
        + 6676825238845503608794865053193017342067) * 10^40
        + 3328908509612125965209274525519979937455) * 10^40
        + 7850446414824324123497000939313712874015) : ℚ) /
        (((((((1017838595347904582228050189 * 10^40
        + 7215040244537784357540472426737951504922) * 10^40
        + 1449501049214412855029207765817140209220) * 10^40
        + 405440434596874258465945390091365612565) * 10^40
        + 7182850692608730807372005648528705437642) * 10^40
        + 6996653892326793448164654227331998304002) * 10^40
        + 3661430118361181573054327851251262288179) * 10^40
        + 2194693300905032524739563836876294979584)),
    (((-((((193 * 10^40
        + 2061916276997054727460114241811586763519) * 10^40
        + 3748774140341043132422421870209721339512) * 10^40
        + 429878511090693373120227503448751370773) * 10^40
        + 1132385966551288353045958397569590343547)) : ℚ) /
        (((1063452759932843875988326949091362 * 10^40
        + 4157367648379732903007408505123337206247) * 10^40
        + 2157512169091279072525066138099559898953) * 10^40
        + 2964581389492981839164223672409470795776)))

noncomputable def corrC02701MinusMidpointP026Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP026BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP026Center2572‖ ≤
          corrC02701MinusMidpointP026Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP026Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP026Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP026Input2572 15 =
      (corrC02701MinusMidpointP026Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP026Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP026Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP026Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP026Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP026Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP026Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP026DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP026Factor2572 * embedPair2542
          corrC02701MinusMidpointP026Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP026Factor2572 : ℝ) *
            corrC02701MinusMidpointP026Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP026Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP026Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP026BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP026Factor2572)

def corrC02701MinusMidpointP027Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((211090470366057865778518799 : ℚ) /
        29514790517935282585600000000))

def corrC02701MinusMidpointP027Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP027Factor2572 : RatPair2542 := (((((((((((64 * 10^40
        + 6805805118825326863182836760309457376470) * 10^40
        + 2757026064444469694267264689457439645870) * 10^40
        + 9228099529993109585085164623748983925189) * 10^40
        + 3675333332862894480147012344423356132068) * 10^40
        + 6695960836609229112986322311649503961363) * 10^40
        + 4499923440331522176426572917514880642261) * 10^40
        + 8895704705159115373739114576304653964254) * 10^40
        + 1237138786480648455312479308313698500863) : ℚ) /
        (((((((4071354381391618328912200758 * 10^40
        + 8860160978151137430161889706951806019688) * 10^40
        + 5798004196857651420116831063268560836880) * 10^40
        + 1621761738387497033863781560365462450262) * 10^40
        + 8731402770434923229488022594114821750570) * 10^40
        + 7986615569307173792658616909327993216009) * 10^40
        + 4645720473444726292217311405005049152716) * 10^40
        + 8778773203620130098958255347505179918336)),
    (((-((((1217 * 10^40
        + 7487319027748419154174147004906011419153) * 10^40
        + 2798339172546461002908894370946981603969) * 10^40
        + 2503346280975819280838954212550380185527) * 10^40
        + 742232713822640801844702074119567581311)) : ℚ) /
        (((6380716559597063255929961694548174 * 10^40
        + 4944205890278397418044451030740023237483) * 10^40
        + 2945073014547674435150396828597359393719) * 10^40
        + 7787488336957891034985342034456824774656)))

noncomputable def corrC02701MinusMidpointP027Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP027BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP027Center2572‖ ≤
          corrC02701MinusMidpointP027Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP027Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP027Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP027Input2572 15 =
      (corrC02701MinusMidpointP027Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP027Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP027Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP027Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP027Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP027Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP027Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP027DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP027Factor2572 * embedPair2542
          corrC02701MinusMidpointP027Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP027Factor2572 : ℝ) *
            corrC02701MinusMidpointP027Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP027Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP027Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP027BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP027Factor2572)

def corrC02701MinusMidpointP028Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((860424389879986254866272499 : ℚ) /
        118059162071741130342400000000))

def corrC02701MinusMidpointP028Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP028Factor2572 : RatPair2542 := (((((((((((1034 * 10^40
        + 8892881886865844414437374986373739931277) * 10^40
        + 7318659685991376600856402175232515659509) * 10^40
        + 2926320411435202792207217307513698103501) * 10^40
        + 4282046554691733166127241087683764505715) * 10^40
        + 4743764848907958700200057216679576587249) * 10^40
        + 9272652514859616615177063910821872047776) * 10^40
        + 9598831474861134925248625353514265927015) * 10^40
        + 5487828628339782578131156946205378260023) : ℚ) /
        (((((((65141670102265893262595212142 * 10^40
        + 1762575650418198882590235311228896315017) * 10^40
        + 2768067149722422721869297012296973390082) * 10^40
        + 5948187814199952541820504965847399204205) * 10^40
        + 9702444326958771671808361505837148009132) * 10^40
        + 7785849108914780682537870549247891456151) * 10^40
        + 4331527575115620675476982480080786443470) * 10^40
        + 460371257922081583332085560082878693376)),
    (((-((((4963 * 10^40
        + 6570891030100800924693121261119586470998) * 10^40
        + 5598846536584349538736910163377657594680) * 10^40
        + 8368900687132179013061112961314570667118) * 10^40
        + 8410422470377920162881730538431025320611)) : ℚ) /
        (((25522866238388253023719846778192697 * 10^40
        + 9776823561113589672177804122960092949933) * 10^40
        + 1780292058190697740601587314389437574879) * 10^40
        + 1149953347831564139941368137827299098624)))

noncomputable def corrC02701MinusMidpointP028Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP028BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP028Center2572‖ ≤
          corrC02701MinusMidpointP028Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP028Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP028Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP028Input2572 15 =
      (corrC02701MinusMidpointP028Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP028Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP028Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP028Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP028Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP028Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP028Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP028DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP028Factor2572 * embedPair2542
          corrC02701MinusMidpointP028Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP028Factor2572 : ℝ) *
            corrC02701MinusMidpointP028Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP028Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP028Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP028BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP028Factor2572)

def corrC02701MinusMidpointP029Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((884878527656961808081806583 : ℚ) /
        118059162071741130342400000000))

def corrC02701MinusMidpointP029Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def corrC02701MinusMidpointP029Factor2572 : RatPair2542 := (((((((((((1034 * 10^40
        + 8892881864516211252537173202174755873595) * 10^40
        + 4957511092689140451753120263694838409126) * 10^40
        + 7648830012332647141989919595744404397215) * 10^40
        + 681030321896324824825677830593959177923) * 10^40
        + 471007642599173726701373952056256906413) * 10^40
        + 8311265756678406571699053934241558897608) * 10^40
        + 5558618213473746478236195670322923160505) * 10^40
        + 7000665383329770620786090526519150040975) : ℚ) /
        (((((((65141670102265893262595212142 * 10^40
        + 1762575650418198882590235311228896315017) * 10^40
        + 2768067149722422721869297012296973390082) * 10^40
        + 5948187814199952541820504965847399204205) * 10^40
        + 9702444326958771671808361505837148009132) * 10^40
        + 7785849108914780682537870549247891456151) * 10^40
        + 4331527575115620675476982480080786443470) * 10^40
        + 460371257922081583332085560082878693376)),
    (((-((((5104 * 10^40
        + 7292806427187934053079018020458330007609) * 10^40
        + 1884518742353653386507993917539043040700) * 10^40
        + 3908166851862419866054065768344515089063) * 10^40
        + 5683529437189000400924421215964017325287)) : ℚ) /
        (((25522866238388253023719846778192697 * 10^40
        + 9776823561113589672177804122960092949933) * 10^40
        + 1780292058190697740601587314389437574879) * 10^40
        + 1149953347831564139941368137827299098624)))

noncomputable def corrC02701MinusMidpointP029Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem corrC02701MinusMidpointP029BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP029Center2572‖ ≤
          corrC02701MinusMidpointP029Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 corrC02701MinusMidpointP029Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, corrC02701MinusMidpointP029Input2572]
  have hs : compactExp2547 corrC02701MinusMidpointP029Input2572 15 =
      (corrC02701MinusMidpointP029Center2572, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 corrC02701MinusMidpointP029Input2572 15).2 : ℝ) =
      corrC02701MinusMidpointP029Error2572 :=
      by
    rw [hs]
    norm_num [corrC02701MinusMidpointP029Error2572]
  have h := compactExp_error2547 corrC02701MinusMidpointP029Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          corrC02701MinusMidpointP029Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
        nodeModulation2541,
      embedPair2542, corrC02701MinusMidpointP029Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem corrC02701MinusMidpointP029DerivativeError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP029Factor2572 * embedPair2542
          corrC02701MinusMidpointP029Center2572‖ ≤
        (pairMagnitude2542 corrC02701MinusMidpointP029Factor2572 : ℝ) *
            corrC02701MinusMidpointP029Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 = embedPair2542
          corrC02701MinusMidpointP029Factor2572 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      corrC02701MinusMidpointP029Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ corrC02701MinusMidpointP029BaseError2572
    (embedPair_magnitude2542 corrC02701MinusMidpointP029Factor2572)

theorem corrC02701MinusMidpointGrid2572 :
    -stripRadius2303 + ((5403 : ℝ) /
        2) * (2 * stripRadius2303 / 10240) =
      corrC02701MinusMidpointPosition2572 := by
  norm_num [stripRadius2303, corrC02701MinusMidpointPosition2572]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP000DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP001DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP002DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP003DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP004DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP005DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP006DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP007DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP008DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP009DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP010DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP011DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP012DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP013DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP014DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP015DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP016DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP017DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP018DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP019DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP020DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP021DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP022DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP023DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP024DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP025DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP026DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP027DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP028DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointP029DerivativeError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusMidpointGrid2572
