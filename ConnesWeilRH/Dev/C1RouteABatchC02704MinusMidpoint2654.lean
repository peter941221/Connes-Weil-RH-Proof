import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchC02704MinusMidpointPosition2654 : ℝ := (((-316604420831) : ℝ) /
        102400000000)

theorem batchC02704MinusMidpointZero2654 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchC02704MinusMidpointP000Center2654 : RatPair2542 := (0, 0)

def batchC02704MinusMidpointP000Factor2654 : RatPair2542 := (0, 0)

noncomputable def batchC02704MinusMidpointP000Error2654 : ℝ := 0

theorem batchC02704MinusMidpointP000Exterior2654 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02704MinusMidpointPosition2654 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |batchC02704MinusMidpointPosition2654| := by
    norm_num [storedWidth, batchC02704MinusMidpointPosition2654]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem batchC02704MinusMidpointP000BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP000Center2654‖ ≤
          batchC02704MinusMidpointP000Error2654 := by
  rw [batchC02704MinusMidpointP000Exterior2654]
  norm_num [batchC02704MinusMidpointP000Center2654, batchC02704MinusMidpointP000Error2654,
      batchC02704MinusMidpointZero2654]

theorem batchC02704MinusMidpointP000DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP000Factor2654 * embedPair2542
          batchC02704MinusMidpointP000Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP000Factor2654 : ℝ) *
            batchC02704MinusMidpointP000Error2654 := by
  rw [batchC02704MinusMidpointP000Exterior2654]
  norm_num [batchC02704MinusMidpointP000Factor2654, batchC02704MinusMidpointP000Center2654,
      batchC02704MinusMidpointP000Error2654,
      batchC02704MinusMidpointZero2654, pairMagnitude2542]

def batchC02704MinusMidpointP001Input2654 : RatPair2542 := ((((-((668 * 10^40
        + 7605061020145841264625370696995567026342) * 10^40
        + 2170605920570883468611667846601337798401)) : ℚ) /
        ((1911 * 10^40
        + 636059313002481026974552982466043868025) * 10^40
        + 9490129860940691830087093216870400000000)),
    ((1749014960699347497459862099 : ℚ) /
        7378697629483820646400000000))

def batchC02704MinusMidpointP001Center2654 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP001Factor2654 : RatPair2542 :=
    ((((((((((7403231066451951283552153942518 * 10^40
        + 6524811249326710831736727161605442469005) * 10^40
        + 1873638594349246932734309253373288214544) * 10^40
        + 7728072078031518341219362870368314275845) * 10^40
        + 7869683723163308934483631829699144391050) * 10^40
        + 8773624996336699986123893410051807471016) * 10^40
        + 9349203025243109363864842333138846468873) * 10^40
        + 5705364616391600158211944196534584362455) : ℚ) /
        (((((((21853475072466884179775610 * 10^40
        + 5050691844828309978948358444045579402574) * 10^40
        + 5124429258150412373421189788125612843852) * 10^40
        + 3879206421653859396013998052716482817911) * 10^40
        + 5129388763405711352374537319737238752720) * 10^40
        + 7733405148124574933466135533777864478625) * 10^40
        + 4933855586968653219817805121510767357912) * 10^40
        + 4796348112336791170839587633781595439104)),
    (((-(((21534494086544582557093278129303438887 * 10^40
        + 13655862320975583643315602803965207897) * 10^40
        + 2220095982021533331555735030307449630771) * 10^40
        + 3585228095388820462211696373100405442611)) : ℚ) /
        (((467477005557138437737010044212394 * 10^40
        + 6044292994922824666019867359004322520904) * 10^40
        + 5872892945262257961704847409476977725520) * 10^40
        + 8632871452613278619213937081947781070848)))

noncomputable def batchC02704MinusMidpointP001Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP001BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP001Center2654‖ ≤
          batchC02704MinusMidpointP001Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP001Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP001Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP001Input2654 9 =
      (batchC02704MinusMidpointP001Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP001Input2654 9).2 : ℝ) =
      batchC02704MinusMidpointP001Error2654 := by
    rw [hs]
    norm_num [batchC02704MinusMidpointP001Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP001Input2654 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          batchC02704MinusMidpointP001Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP001Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP001DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP001Factor2654 * embedPair2542
          batchC02704MinusMidpointP001Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP001Factor2654 : ℝ) *
            batchC02704MinusMidpointP001Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP001Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP001Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP001BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP001Factor2654)

def batchC02704MinusMidpointP002Input2654 : RatPair2542 := ((((-((17179 * 10^40
        + 6167013373080278089489083252611035580143) * 10^40
        + 6169887229220783560141729732785711415041)) : ℚ) /
        ((73583 * 10^40
        + 7987996688174414725693033560276360199885) * 10^40
        + 3720647135657254640696745734963200000000)),
    (((-1749014960699347497459862099) : ℚ) /
        3689348814741910323200000000))

def batchC02704MinusMidpointP002Center2654 : RatPair2542 := ((((-402844658968142621323) : ℚ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)),
    (((-14790371207753118777897) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC02704MinusMidpointP002Factor2654 : RatPair2542 :=
    ((((((((((48204047293513549249616198138866427 *
    10^40
        + 1681170487922032572928060195694446209631) * 10^40
        + 3606353883719961964579958152738163954961) * 10^40
        + 7128514917515453174984305203162209194832) * 10^40
        + 2058897267675977386026059246145999877266) * 10^40
        + 9769222870689620908671049042002154621905) * 10^40
        + 1140263319162295248100633485329126392580) * 10^40
        + 2311657747175577855635285168249049335255) : ℚ) /
        (((((((768544007996139530741708440094330 * 10^40
        + 9361303830205268585602265894693607351812) * 10^40
        + 824868157390208916240674428880399579936) * 10^40
        + 9148246831777139172358148600830896877111) * 10^40
        + 9608280519287181024184822336117609032452) * 10^40
        + 9688365701619582451736214667915733094333) * 10^40
        + 3844663304948024323402919916110603427146) * 10^40
        + 334390143674563506184767510638697119744)),
    (((((8901219281759249731715994055386198757327 * 10^40
        + 7335253932900430305588191845719758582796) * 10^40
        + 5534547029400237140518023078551697603938) * 10^40
        + 630023067231302865015569089845150730291) : ℚ) /
        (((2772262628244552754429238432031480309 * 10^40
        + 6223291736604392270002797445474580939063) * 10^40
        + 4032601404758650854844934471541382160839) * 10^40
        + 1300403566374860875657492978631954137088)))

noncomputable def batchC02704MinusMidpointP002Error2654 : ℝ := ((60534243797693441867 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP002BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP002Center2654‖ ≤
          batchC02704MinusMidpointP002Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP002Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP002Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP002Input2654 8 =
      (batchC02704MinusMidpointP002Center2654, ((60534243797693441867 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP002Input2654 8).2 : ℝ) =
      batchC02704MinusMidpointP002Error2654 := by
    rw [hs]
    norm_num [batchC02704MinusMidpointP002Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP002Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02704MinusMidpointP002Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP002Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP002DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP002Factor2654 * embedPair2542
          batchC02704MinusMidpointP002Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP002Factor2654 : ℝ) *
            batchC02704MinusMidpointP002Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP002Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP002Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP002BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP002Factor2654)

def batchC02704MinusMidpointP003Input2654 : RatPair2542 := ((((-((2247301 * 10^40
        + 2965784959016823649534340676575741235749) * 10^40
        + 611880493725806969820777196137299213707)) : ℚ) /
        ((13308535 * 10^40
        + 6751979202907900655116715595283540785903) * 10^40
        + 7472841032378766672788969383526400000000)),
    (((-1749014960699347497459862099) : ℚ) /
        3689348814741910323200000000))

def batchC02704MinusMidpointP003Center2654 : RatPair2542 := ((((-24565477871329862221911841057) :
    ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-28184913257217396655567940129) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)))

def batchC02704MinusMidpointP003Factor2654 : RatPair2542 := ((((-((((((((112253 * 10^40
        + 281933113380823788007185275910194685671) * 10^40
        + 7282269247617033501108355150986592989588) * 10^40
        + 7102081541628652624519393150993573512529) * 10^40
        + 8496083109210176708033208979030398902456) * 10^40
        + 9943207793576163254141674007482349556877) * 10^40
        + 6044835166816805714760086615507421405485) * 10^40
        + 2978032930024596139322734551197695040268) * 10^40
        + 8362596132303947837752140256690335971545)) : ℚ) /
        ((((((((82 * 10^40
        + 2358175674475107282863083607165231438553) * 10^40
        + 3981180535562814828914998184550481696527) * 10^40
        + 6425835897100049067887745617052251523739) * 10^40
        + 4793375341035515417090652618239022416240) * 10^40
        + 8169336364903877106445059434992959303810) * 10^40
        + 7640161759965414941666596179419423873696) * 10^40
        + 3779308659828157348964790050369598712326) * 10^40
        + 3328168814931870165704778965448763899904)),
    ((((((29395 * 10^40
        + 9151453783170721181159116446337979748362) * 10^40
        + 6537341195830324641894296869457375983844) * 10^40
        + 9765756544447943403725970372566009996902) * 10^40
        + 2493309453906088169412147451162164257617) : ℚ) /
        ((((27 * 10^40
        + 2051899112472213698474640440590205680089) * 10^40
        + 7970833192203484612734256613353969058935) * 10^40
        + 3927699987012224977035553582790784574541) * 10^40
        + 7976106969681169150836269207915442733056)))

noncomputable def batchC02704MinusMidpointP003Error2654 : ℝ := ((865106607369422343193407201 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP003BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP003Center2654‖ ≤
          batchC02704MinusMidpointP003Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP003Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP003Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP003Input2654 8 =
      (batchC02704MinusMidpointP003Center2654, ((865106607369422343193407201 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP003Input2654 8).2 : ℝ) =
      batchC02704MinusMidpointP003Error2654 := by
    rw [hs]
    norm_num [batchC02704MinusMidpointP003Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP003Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02704MinusMidpointP003Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP003Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP003DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP003Factor2654 * embedPair2542
          batchC02704MinusMidpointP003Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP003Factor2654 : ℝ) *
            batchC02704MinusMidpointP003Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP003Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP003Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP003BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP003Factor2654)

def batchC02704MinusMidpointP004Input2654 : RatPair2542 := ((((-((38819 * 10^40
        + 8447418257706986303756449715685516563010) * 10^40
        + 6542164360536221076761859786496648915041)) : ℚ) /
        ((268279 * 10^40
        + 8980219141639860859523318093054262845938) * 10^40
        + 634976154003494640696745734963200000000)),
    ((1749014960699347497459862099 : ℚ) /
        3689348814741910323200000000))

def batchC02704MinusMidpointP004Center2654 : RatPair2542 := ((((-1491485382364416700627589482419)
    : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    ((54759624994436920431826137597241 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC02704MinusMidpointP004Factor2654 : RatPair2542 :=
    ((((-(((((((203905400867473186956956004326190320659 *
    10^40
        + 8412214495514633444210920124540871344931) * 10^40
        + 994733169305550309730822192738112359467) * 10^40
        + 9565585687213501455630922498251991714940) * 10^40
        + 3961734018113051548580042023069017983027) * 10^40
        + 4265971452604605995732774581380874893792) * 10^40
        + 2883166397814428427729744069812625123408) * 10^40
        + 3061996654938588641849579577844700664745)) : ℚ) /
        (((((((135797711855174546482627411704474083 * 10^40
        + 1438932361118371236678249609145534498703) * 10^40
        + 3302699898076317607206904280069547593226) * 10^40
        + 2258701786778009398077322959449149630908) * 10^40
        + 8578896788391039550319641454524174194249) * 10^40
        + 3658190695994485095205099368695549884643) * 10^40
        + 9587944744639141328784841006591277057687) * 10^40
        + 4299101381236757914427967510638697119744)),
    (((-((((1 * 10^40
        + 9227927675922417695404023957212682501529) * 10^40
        + 6566343412571608718324657173801292833518) * 10^40
        + 3836505491669917172441025731005902417119) * 10^40
        + 2813764477571150844201471287110775730291)) : ℚ) /
        (((36850741085516115639482908674473160594 * 10^40
        + 2340907442513691956545070470149820779182) * 10^40
        + 2352016578379110011499844513941403404846) * 10^40
        + 9829185100112973732540692978631954137088)))

noncomputable def batchC02704MinusMidpointP004Error2654 : ℝ := ((205083026639790813025677559395 :
    ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC02704MinusMidpointP004BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP004Center2654‖ ≤
          batchC02704MinusMidpointP004Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP004Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP004Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP004Input2654 8 =
      (batchC02704MinusMidpointP004Center2654, ((205083026639790813025677559395 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP004Input2654 8).2 : ℝ) =
      batchC02704MinusMidpointP004Error2654 := by
    rw [hs]
    norm_num [batchC02704MinusMidpointP004Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP004Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02704MinusMidpointP004Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP004Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP004DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP004Factor2654 * embedPair2542
          batchC02704MinusMidpointP004Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP004Factor2654 : ℝ) *
            batchC02704MinusMidpointP004Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP004Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP004Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP004BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP004Factor2654)

def batchC02704MinusMidpointP005Center2654 : RatPair2542 := (0, 0)

def batchC02704MinusMidpointP005Factor2654 : RatPair2542 := (0, 0)

noncomputable def batchC02704MinusMidpointP005Error2654 : ℝ := 0

theorem batchC02704MinusMidpointP005Exterior2654 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02704MinusMidpointPosition2654 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |batchC02704MinusMidpointPosition2654| := by
    norm_num [storedWidth, batchC02704MinusMidpointPosition2654]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem batchC02704MinusMidpointP005BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP005Center2654‖ ≤
          batchC02704MinusMidpointP005Error2654 := by
  rw [batchC02704MinusMidpointP005Exterior2654]
  norm_num [batchC02704MinusMidpointP005Center2654, batchC02704MinusMidpointP005Error2654,
      batchC02704MinusMidpointZero2654]

theorem batchC02704MinusMidpointP005DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP005Factor2654 * embedPair2542
          batchC02704MinusMidpointP005Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP005Factor2654 : ℝ) *
            batchC02704MinusMidpointP005Error2654 := by
  rw [batchC02704MinusMidpointP005Exterior2654]
  norm_num [batchC02704MinusMidpointP005Factor2654, batchC02704MinusMidpointP005Center2654,
      batchC02704MinusMidpointP005Error2654,
      batchC02704MinusMidpointZero2654, pairMagnitude2542]

def batchC02704MinusMidpointP006Input2654 : RatPair2542 :=
    ((((-336470217059869907721429413470905397) : ℚ) /
        590119355113074880408793907200000000),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP006Center2654 : RatPair2542 := (((29447473184781467 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP006Factor2654 : RatPair2542 := (((((150642529928315 * 10^40
        + 8812368343129870275841615499972419282707) * 10^40
        + 6694201799891541537329842547866493252883) : ℚ) /
        ((30816335580 * 10^40
        + 6749904453217039673672739966804559017622) * 10^40
        + 7356208886278486149319370191465973011532)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP006Error2654 : ℝ := ((9528633610675 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP006BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP006Center2654‖ ≤
          batchC02704MinusMidpointP006Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP006Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP006Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP006Input2654 7 =
      (batchC02704MinusMidpointP006Center2654, ((9528633610675 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP006Input2654 7).2 : ℝ) =
      batchC02704MinusMidpointP006Error2654 := by
    rw [hs]
    norm_num [batchC02704MinusMidpointP006Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP006Input2654 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          batchC02704MinusMidpointP006Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP006Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP006DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP006Factor2654 * embedPair2542
          batchC02704MinusMidpointP006Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP006Factor2654 : ℝ) *
            batchC02704MinusMidpointP006Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP006Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP006Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP006BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP006Factor2654)

def batchC02704MinusMidpointP007Input2654 : RatPair2542 := ((((-((2247301 * 10^40
        + 2965784959016823649534340676575741235749) * 10^40
        + 611880493725806969820777196137299213707)) : ℚ) /
        ((3327133 * 10^40
        + 9187994800726975163779178898820885196475) * 10^40
        + 9368210258094691668197242345881600000000)),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP007Center2654 : RatPair2542 := (((61489999547196883826002322453 : ℚ)
    /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP007Factor2654 : RatPair2542 := ((((((((((29185977136539498 * 10^40
        + 5046140803941644648216287340750009053528) * 10^40
        + 5547490334110652648546964946288736136182) * 10^40
        + 5810801024851559883899257707139099565891) * 10^40
        + 8415760736989402639388086975056717394396) * 10^40
        + 4514610860214848787540789670537294348383) * 10^40
        + 1740945242465993770775982631120122709109) * 10^40
        + 4989188071097014332933128757255361058481) : ℚ) /
        (((((((166073911008887 * 10^40
        + 3686098029186131492750394246691174983621) * 10^40
        + 9593704170529650296151592633682882948920) * 10^40
        + 8714322671097619071294065744365639540343) * 10^40
        + 6184907631291433971744015629852755707844) * 10^40
        + 6925434780709448943521335074897692892749) * 10^40
        + 2257878692397432355797575177357094599804) * 10^40
        + 1884176284388057331732515029021444233924)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP007Error2654 : ℝ := ((2125528980386611621221397 : ℝ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))

theorem batchC02704MinusMidpointP007BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP007Center2654‖ ≤
          batchC02704MinusMidpointP007Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP007Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP007Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP007Input2654 6 =
      (batchC02704MinusMidpointP007Center2654, ((2125528980386611621221397 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP007Input2654 6).2 : ℝ) =
      batchC02704MinusMidpointP007Error2654 := by
    rw [hs]
    norm_num [batchC02704MinusMidpointP007Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP007Input2654 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          batchC02704MinusMidpointP007Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP007Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP007DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP007Factor2654 * embedPair2542
          batchC02704MinusMidpointP007Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP007Factor2654 : ℝ) *
            batchC02704MinusMidpointP007Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP007Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP007Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP007BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP007Factor2654)

def batchC02704MinusMidpointP008Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((782182 * 10^40
        + 5320360220295712195426977782364918186105) * 10^40
        + 7018763413979605529247020272844800000000)),
    ((1259633303355652447930297807 : ℚ) /
        236118324143482260684800000000))

def batchC02704MinusMidpointP008Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP008Factor2654 : RatPair2542 := (((((((((((7339 * 10^40
        + 7485945212872874837902570813367703951649) * 10^40
        + 3469229790506767651382629777640977656013) * 10^40
        + 2903843199683481845882803733245296239325) * 10^40
        + 384784944141163001201458576266701663726) * 10^40
        + 7839957804717617927241835056672764397386) * 10^40
        + 9005598589815297271064799358521578675747) * 10^40
        + 3428323086813219423067588487196476376280) * 10^40
        + 6171854206461368567193179829913165515375) : ℚ) /
        (((((((37431088071401022787876687451650 * 10^40
        + 8858328990043098182625486466189732850683) * 10^40
        + 8162083399804228211306898734880250559685) * 10^40
        + 3248965923095590960209580801207438606103) * 10^40
        + 7254694828108098488964314238090827012228) * 10^40
        + 2864604255304149805741251312032893842465) * 10^40
        + 3163528875121834545080891702386802722463) * 10^40
        + 6560550514417518511948075861795055599616)),
    (((-((((7266 * 10^40
        + 6301248586747822313418347758650902951939) * 10^40
        + 1352386163434770211605657620055098688147) * 10^40
        + 8396631111881334249611233834555790327625) * 10^40
        + 4583320176705630023476549648343651794181)) : ℚ) /
        (((1835428540266847885790665017254671196 * 10^40
        + 3354248017055075352947552387349794627589) * 10^40
        + 9310757741648150980929840177778629741840) * 10^40
        + 5585090816207732058487898415830885466112)))

noncomputable def batchC02704MinusMidpointP008Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP008BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP008Center2654‖ ≤
          batchC02704MinusMidpointP008Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP008Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP008Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP008Input2654 13 =
      (batchC02704MinusMidpointP008Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP008Input2654 13).2 : ℝ) =
      batchC02704MinusMidpointP008Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP008Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP008Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchC02704MinusMidpointP008Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP008Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP008DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP008Factor2654 * embedPair2542
          batchC02704MinusMidpointP008Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP008Factor2654 : ℝ) *
            batchC02704MinusMidpointP008Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP008Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP008Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP008BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP008Factor2654)

def batchC02704MinusMidpointP009Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((782182 * 10^40
        + 5320360220295712195426977782364918186105) * 10^40
        + 7018763413979605529247020272844800000000)),
    ((1873404750918948301439333841 : ℚ) /
        236118324143482260684800000000))

def batchC02704MinusMidpointP009Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP009Factor2654 : RatPair2542 := (((((((((((7339 * 10^40
        + 7485936149470322300531096091805399080623) * 10^40
        + 8312863364295523486899103150819171558719) * 10^40
        + 7955563141141863090104602175738515535769) * 10^40
        + 7448320860289114298189176482440877504325) * 10^40
        + 9787016153261582914097580407125433501683) * 10^40
        + 1865939198254655859765348144803944620610) * 10^40
        + 5897941396548665403703120096059632407661) * 10^40
        + 9053170755144478551183241674275574720303) : ℚ) /
        (((((((37431088071401022787876687451650 * 10^40
        + 8858328990043098182625486466189732850683) * 10^40
        + 8162083399804228211306898734880250559685) * 10^40
        + 3248965923095590960209580801207438606103) * 10^40
        + 7254694828108098488964314238090827012228) * 10^40
        + 2864604255304149805741251312032893842465) * 10^40
        + 3163528875121834545080891702386802722463) * 10^40
        + 6560550514417518511948075861795055599616)),
    (((-((((3602 * 10^40
        + 4609603485847840698307112256239738612791) * 10^40
        + 9706023393736357332483918854204987299221) * 10^40
        + 457872455904832098753989932463674913554) * 10^40
        + 9966279429801673285476301431535858569801)) : ℚ) /
        (((611809513422282628596888339084890398 * 10^40
        + 7784749339018358450982517462449931542529) * 10^40
        + 9770252580549383660309946725926209913946) * 10^40
        + 8528363605402577352829299471943628488704)))

noncomputable def batchC02704MinusMidpointP009Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP009BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP009Center2654‖ ≤
          batchC02704MinusMidpointP009Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP009Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP009Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP009Input2654 13 =
      (batchC02704MinusMidpointP009Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP009Input2654 13).2 : ℝ) =
      batchC02704MinusMidpointP009Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP009Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP009Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchC02704MinusMidpointP009Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP009Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP009DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP009Factor2654 * embedPair2542
          batchC02704MinusMidpointP009Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP009Factor2654 : ℝ) *
            batchC02704MinusMidpointP009Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP009Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP009Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP009BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP009Factor2654)

def batchC02704MinusMidpointP010Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((782182 * 10^40
        + 5320360220295712195426977782364918186105) * 10^40
        + 7018763413979605529247020272844800000000)),
    ((1114436568009919590097554951 : ℚ) /
        118059162071741130342400000000))

def batchC02704MinusMidpointP010Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP010Factor2654 : RatPair2542 := (((((((((((1834 * 10^40
        + 9371482319122994073600147000532574876237) * 10^40
        + 2416323982674114025635862286992252399892) * 10^40
        + 5293406952629542189948096968477331433602) * 10^40
        + 1493399409532825074647257594548635536820) * 10^40
        + 8094953981641072457433571404864969530195) * 10^40
        + 2272320162650753904638170790033719982458) * 10^40
        + 4551987714624763677687271233412009175370) * 10^40
        + 9329501153793609502725740986128459549855) : ℚ) /
        (((((((9357772017850255696969171862912 * 10^40
        + 7214582247510774545656371616547433212670) * 10^40
        + 9540520849951057052826724683720062639921) * 10^40
        + 3312241480773897740052395200301859651525) * 10^40
        + 9313673707027024622241078559522706753057) * 10^40
        + 716151063826037451435312828008223460616) * 10^40
        + 3290882218780458636270222925596700680615) * 10^40
        + 9140137628604379627987018965448763899904)),
    (((-((((2143 * 10^40
        + 41890687454416686008046462978041590180) * 10^40
        + 490015802057454999015025889245676619293) * 10^40
        + 3922907211735407796574014123567122064684) * 10^40
        + 1255039798549941199158341949600332962511)) : ℚ) /
        (((305904756711141314298444169542445199 * 10^40
        + 3892374669509179225491258731224965771264) * 10^40
        + 9885126290274691830154973362963104956973) * 10^40
        + 4264181802701288676414649735971814244352)))

noncomputable def batchC02704MinusMidpointP010Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP010BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP010Center2654‖ ≤
          batchC02704MinusMidpointP010Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP010Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP010Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP010Input2654 13 =
      (batchC02704MinusMidpointP010Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP010Input2654 13).2 : ℝ) =
      batchC02704MinusMidpointP010Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP010Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP010Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchC02704MinusMidpointP010Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP010Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP010DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP010Factor2654 * embedPair2542
          batchC02704MinusMidpointP010Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP010Factor2654 : ℝ) *
            batchC02704MinusMidpointP010Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP010Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP010Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP010BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP010Factor2654)

def batchC02704MinusMidpointP011Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((782182 * 10^40
        + 5320360220295712195426977782364918186105) * 10^40
        + 7018763413979605529247020272844800000000)),
    ((1232937275700447526054176631 : ℚ) /
        118059162071741130342400000000))

def batchC02704MinusMidpointP011Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP011Factor2654 : RatPair2542 := (((((((((((1834 * 10^40
        + 9371481008064334360181631150224865308288) * 10^40
        + 2831893118778900822633686408473927114743) * 10^40
        + 5651032883149850376166745871600961119211) * 10^40
        + 1591178343183989057917809810557728802158) * 10^40
        + 6016222987098055883927445574524679723239) * 10^40
        + 9849888018786735996443218300227556475915) * 10^40
        + 8963692881982372502247429770927269065395) * 10^40
        + 4321361211600690844332684660885407424895) : ℚ) /
        (((((((9357772017850255696969171862912 * 10^40
        + 7214582247510774545656371616547433212670) * 10^40
        + 9540520849951057052826724683720062639921) * 10^40
        + 3312241480773897740052395200301859651525) * 10^40
        + 9313673707027024622241078559522706753057) * 10^40
        + 716151063826037451435312828008223460616) * 10^40
        + 3290882218780458636270222925596700680615) * 10^40
        + 9140137628604379627987018965448763899904)),
    (((-((((7112 * 10^40
        + 6248613771645387061163961915574714226001) * 10^40
        + 7179374021224213320051475944021901300841) * 10^40
        + 1736987020684466343934414723263430612945) * 10^40
        + 5164757453809918594119181860166473574973)) : ℚ) /
        (((917714270133423942895332508627335598 * 10^40
        + 1677124008527537676473776193674897313794) * 10^40
        + 9655378870824075490464920088889314870920) * 10^40
        + 2792545408103866029243949207915442733056)))

noncomputable def batchC02704MinusMidpointP011Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP011BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP011Center2654‖ ≤
          batchC02704MinusMidpointP011Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP011Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP011Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP011Input2654 13 =
      (batchC02704MinusMidpointP011Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP011Input2654 13).2 : ℝ) =
      batchC02704MinusMidpointP011Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP011Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP011Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchC02704MinusMidpointP011Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP011Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP011DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP011Factor2654 * embedPair2542
          batchC02704MinusMidpointP011Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP011Factor2654 : ℝ) *
            batchC02704MinusMidpointP011Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP011Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP011Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP011BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP011Factor2654)

def batchC02704MinusMidpointP012Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((782182 * 10^40
        + 5320360220295712195426977782364918186105) * 10^40
        + 7018763413979605529247020272844800000000)),
    ((27113500145429484224061979 : ℚ) /
        2361183241434822606848000000))

def batchC02704MinusMidpointP012Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP012Factor2654 : RatPair2542 := (((((((((((458 * 10^40
        + 7342869877643508151209540051099051609446) * 10^40
        + 3475735071558273457925655427782102698918) * 10^40
        + 7362359215468320572322088364641090264910) * 10^40
        + 3340954327644875210870897822140008712730) * 10^40
        + 1493197432419664299722160336646806344676) * 10^40
        + 3618926414858691575530484726440856576473) * 10^40
        + 8279809098617546386864979467812247965416) * 10^40
        + 1218895145241994581440230894807999018119) : ℚ) /
        (((((((2339443004462563924242292965728 * 10^40
        + 1803645561877693636414092904136858303167) * 10^40
        + 7385130212487764263206681170930015659980) * 10^40
        + 3328060370193474435013098800075464912881) * 10^40
        + 4828418426756756155560269639880676688264) * 10^40
        + 2679037765956509362858828207002055865154) * 10^40
        + 822720554695114659067555731399175170153) * 10^40
        + 9785034407151094906996754741362190974976)),
    (((-((((3910 * 10^40
        + 3399462023645553176847901922538627817103) * 10^40
        + 2565735083758786530677011141217230270573) * 10^40
        + 9241372478253831540043009767215338941762) * 10^40
        + 1772925323859430940264114371685038891425)) : ℚ) /
        (((458857135066711971447666254313667799 * 10^40
        + 838562004263768838236888096837448656897) * 10^40
        + 4827689435412037745232460044444657435460) * 10^40
        + 1396272704051933014621974603957721366528)))

noncomputable def batchC02704MinusMidpointP012Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP012BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP012Center2654‖ ≤
          batchC02704MinusMidpointP012Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP012Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP012Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP012Input2654 13 =
      (batchC02704MinusMidpointP012Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP012Input2654 13).2 : ℝ) =
      batchC02704MinusMidpointP012Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP012Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP012Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchC02704MinusMidpointP012Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP012Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP012DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP012Factor2654 * embedPair2542
          batchC02704MinusMidpointP012Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP012Factor2654 : ℝ) *
            batchC02704MinusMidpointP012Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP012Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP012Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP012BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP012Factor2654)

def batchC02704MinusMidpointP013Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((782182 * 10^40
        + 5320360220295712195426977782364918186105) * 10^40
        + 7018763413979605529247020272844800000000)),
    ((293504825937452683545508821 : ℚ) /
        23611832414348226068480000000))

def batchC02704MinusMidpointP013Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP013Factor2654 : RatPair2542 := (((((((((((1834 * 10^40
        + 9371478022265361805581429979060844732874) * 10^40
        + 8766202487417824716419885455832945986896) * 10^40
        + 6314606084221349816082863076402826107575) * 10^40
        + 9528090802849498391818034488759731957320) * 10^40
        + 6948420827192108698408334614822484570003) * 10^40
        + 4397467996569494920246778893758080242015) * 10^40
        + 1700799753755051590253507294935451627942) * 10^40
        + 2239844851176812465221674159812998885951) : ℚ) /
        (((((((9357772017850255696969171862912 * 10^40
        + 7214582247510774545656371616547433212670) * 10^40
        + 9540520849951057052826724683720062639921) * 10^40
        + 3312241480773897740052395200301859651525) * 10^40
        + 9313673707027024622241078559522706753057) * 10^40
        + 716151063826037451435312828008223460616) * 10^40
        + 3290882218780458636270222925596700680615) * 10^40
        + 9140137628604379627987018965448763899904)),
    (((-((((2821 * 10^40
        + 9734058935488369030248314110975497685326) * 10^40
        + 536333631268446368323418617477972041182) * 10^40
        + 2872836949317544853438722298521287392112) * 10^40
        + 391112622381727592794665805874100167905)) : ℚ) /
        (((305904756711141314298444169542445199 * 10^40
        + 3892374669509179225491258731224965771264) * 10^40
        + 9885126290274691830154973362963104956973) * 10^40
        + 4264181802701288676414649735971814244352)))

noncomputable def batchC02704MinusMidpointP013Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP013BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP013Center2654‖ ≤
          batchC02704MinusMidpointP013Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP013Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP013Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP013Input2654 13 =
      (batchC02704MinusMidpointP013Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP013Input2654 13).2 : ℝ) =
      batchC02704MinusMidpointP013Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP013Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP013Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchC02704MinusMidpointP013Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP013Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP013DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP013Factor2654 * embedPair2542
          batchC02704MinusMidpointP013Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP013Factor2654 : ℝ) *
            batchC02704MinusMidpointP013Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP013Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP013Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP013BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP013Factor2654)

def batchC02704MinusMidpointP014Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((782182 * 10^40
        + 5320360220295712195426977782364918186105) * 10^40
        + 7018763413979605529247020272844800000000)),
    ((1674769098088922039627248141 : ℚ) /
        118059162071741130342400000000))

def batchC02704MinusMidpointP014Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP014Factor2654 : RatPair2542 := (((((((((((1834 * 10^40
        + 9371474952892681898938532404337308406231) * 10^40
        + 2832425070552563207426081804247923778917) * 10^40
        + 6806084531914377739381829541778671734859) * 10^40
        + 1801681412179458099893134641880890322016) * 10^40
        + 896368756538322762258730219196117128090) * 10^40
        + 5721293289478326356058685911008146897218) * 10^40
        + 3437320445520175507420868885723907049221) * 10^40
        + 1293497535769250743158273476094660580775) : ℚ) /
        (((((((9357772017850255696969171862912 * 10^40
        + 7214582247510774545656371616547433212670) * 10^40
        + 9540520849951057052826724683720062639921) * 10^40
        + 3312241480773897740052395200301859651525) * 10^40
        + 9313673707027024622241078559522706753057) * 10^40
        + 716151063826037451435312828008223460616) * 10^40
        + 3290882218780458636270222925596700680615) * 10^40
        + 9140137628604379627987018965448763899904)),
    (((-((((9661 * 10^40
        + 4844557815117699321047703909041406262396) * 10^40
        + 566963126104499804818501091597385103750) * 10^40
        + 3031219121607795982852919708749370955425) * 10^40
        + 1578600695901457008726388478217001976303)) : ℚ) /
        (((917714270133423942895332508627335598 * 10^40
        + 1677124008527537676473776193674897313794) * 10^40
        + 9655378870824075490464920088889314870920) * 10^40
        + 2792545408103866029243949207915442733056)))

noncomputable def batchC02704MinusMidpointP014Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP014BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP014Center2654‖ ≤
          batchC02704MinusMidpointP014Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP014Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP014Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP014Input2654 13 =
      (batchC02704MinusMidpointP014Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP014Input2654 13).2 : ℝ) =
      batchC02704MinusMidpointP014Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP014Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP014Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchC02704MinusMidpointP014Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP014Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP014DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP014Factor2654 * embedPair2542
          batchC02704MinusMidpointP014Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP014Factor2654 : ℝ) *
            batchC02704MinusMidpointP014Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP014Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP014Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP014BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP014Factor2654)

def batchC02704MinusMidpointP015Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((1823260823309772955292476057 : ℚ) /
        236118324143482260684800000000))

def batchC02704MinusMidpointP015Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP015Factor2654 : RatPair2542 := (((((((((((1834 * 10^40
        + 9371472504705095524322245342450711796275) * 10^40
        + 9441754422715600400425626469155861048250) * 10^40
        + 4262875517786110200016389825409415322237) * 10^40
        + 5991973985197563380341425100351533199145) * 10^40
        + 452155323709682985707799427692781227516) * 10^40
        + 4801167832476453382145407535996992731365) * 10^40
        + 934722986960425137887127106948377525413) * 10^40
        + 1356618761563561896403382451688445572447) : ℚ) /
        (((((((9357772017850255696969171862912 * 10^40
        + 7214582247510774545656371616547433212670) * 10^40
        + 9540520849951057052826724683720062639921) * 10^40
        + 3312241480773897740052395200301859651525) * 10^40
        + 9313673707027024622241078559522706753057) * 10^40
        + 716151063826037451435312828008223460616) * 10^40
        + 3290882218780458636270222925596700680615) * 10^40
        + 9140137628604379627987018965448763899904)),
    (((-((((10518 * 10^40
        + 1103014998913176606835050550476225152200) * 10^40
        + 4221710134840589901618094604275368128960) * 10^40
        + 2848441992979824175053445432639248076721) * 10^40
        + 883203103213269041117836336216701538931)) : ℚ) /
        (((917714270133423942895332508627335598 * 10^40
        + 1677124008527537676473776193674897313794) * 10^40
        + 9655378870824075490464920088889314870920) * 10^40
        + 2792545408103866029243949207915442733056)))

noncomputable def batchC02704MinusMidpointP015Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP015BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP015Center2654‖ ≤
          batchC02704MinusMidpointP015Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP015Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP015Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP015Input2654 14 =
      (batchC02704MinusMidpointP015Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP015Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP015Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP015Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP015Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP015Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP015Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP015DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP015Factor2654 * embedPair2542
          batchC02704MinusMidpointP015Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP015Factor2654 : ℝ) *
            batchC02704MinusMidpointP015Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP015Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP015Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP015BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP015Factor2654)

def batchC02704MinusMidpointP016Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((965286270060315490254887079 : ℚ) /
        118059162071741130342400000000))

def batchC02704MinusMidpointP016Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP016Factor2654 : RatPair2542 := (((((((((((458 * 10^40
        + 7342867651517995196478751201249451440771) * 10^40
        + 9453742201609504035408170956753708763002) * 10^40
        + 2311766322795474530545604366838306242847) * 10^40
        + 8202549469267680073585935196716676901467) * 10^40
        + 9290663566929675324539332643277346282389) * 10^40
        + 7053878066512972887743511057424098451915) * 10^40
        + 5540394850042657855887733124226609118240) * 10^40
        + 375827111475714813041334445735656533983) : ℚ) /
        (((((((2339443004462563924242292965728 * 10^40
        + 1803645561877693636414092904136858303167) * 10^40
        + 7385130212487764263206681170930015659980) * 10^40
        + 3328060370193474435013098800075464912881) * 10^40
        + 4828418426756756155560269639880676688264) * 10^40
        + 2679037765956509362858828207002055865154) * 10^40
        + 822720554695114659067555731399175170153) * 10^40
        + 9785034407151094906996754741362190974976)),
    (((-((((30 * 10^40
        + 4294399839058655063198927077524778048184) * 10^40
        + 5796278527086243350379405356395415091910) * 10^40
        + 8234736021328772348655818471256913605548) * 10^40
        + 8068013005059153615763890311161037271579)) : ℚ) /
        (((2507416038615912412282329258544632 * 10^40
        + 7818789956307452288733534907632991522715) * 10^40
        + 2867910871231759769099630929204615614401) * 10^40
        + 4215280178710666300626349587999768969216)))

noncomputable def batchC02704MinusMidpointP016Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP016BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP016Center2654‖ ≤
          batchC02704MinusMidpointP016Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP016Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP016Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP016Input2654 14 =
      (batchC02704MinusMidpointP016Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP016Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP016Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP016Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP016Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP016Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP016Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP016DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP016Factor2654 * embedPair2542
          batchC02704MinusMidpointP016Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP016Factor2654 : ℝ) *
            batchC02704MinusMidpointP016Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP016Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP016Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP016BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP016Factor2654)

def batchC02704MinusMidpointP017Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((2139018841052257346363716437 : ℚ) /
        236118324143482260684800000000))

def batchC02704MinusMidpointP017Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP017Factor2654 : RatPair2542 := (((((((((((1834 * 10^40
        + 9371466607877494891405152939358311146421) * 10^40
        + 6459117702867260630004057686233963402357) * 10^40
        + 7673227507057564356327374682070114164983) * 10^40
        + 8743265994300460280671067243327786774740) * 10^40
        + 3662810391527743582848479712366103010594) * 10^40
        + 1797840342371366859453259640148674375026) * 10^40
        + 8846410674357736155759944820625173652963) * 10^40
        + 2482868057275768503380565511791037826327) : ℚ) /
        (((((((9357772017850255696969171862912 * 10^40
        + 7214582247510774545656371616547433212670) * 10^40
        + 9540520849951057052826724683720062639921) * 10^40
        + 3312241480773897740052395200301859651525) * 10^40
        + 9313673707027024622241078559522706753057) * 10^40
        + 716151063826037451435312828008223460616) * 10^40
        + 3290882218780458636270222925596700680615) * 10^40
        + 9140137628604379627987018965448763899904)),
    (((-((((4113 * 10^40
        + 2231913904309070471154929763181176429259) * 10^40
        + 2910204621499286435493274384888349312205) * 10^40
        + 5353088999318549048281893779117128296864) * 10^40
        + 7085761279523474361748755032234342666157)) : ℚ) /
        (((305904756711141314298444169542445199 * 10^40
        + 3892374669509179225491258731224965771264) * 10^40
        + 9885126290274691830154973362963104956973) * 10^40
        + 4264181802701288676414649735971814244352)))

noncomputable def batchC02704MinusMidpointP017Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP017BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP017Center2654‖ ≤
          batchC02704MinusMidpointP017Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP017Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP017Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP017Input2654 14 =
      (batchC02704MinusMidpointP017Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP017Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP017Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP017Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP017Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP017Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP017Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP017DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP017Factor2654 * embedPair2542
          batchC02704MinusMidpointP017Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP017Factor2654 : ℝ) *
            batchC02704MinusMidpointP017Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP017Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP017Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP017BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP017Factor2654)

def batchC02704MinusMidpointP018Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((554456987983803044582380403 : ℚ) /
        59029581035870565171200000000))

def batchC02704MinusMidpointP018Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP018Factor2654 : RatPair2542 := (((((((((((114 * 10^40
        + 6835716561846590408051987809945289910083) * 10^40
        + 6025977674572055834448892232507996100038) * 10^40
        + 6656689703033733054196646824144386645149) * 10^40
        + 7761890719184152053901752706023849341798) * 10^40
        + 3692400637859271016808775713420289401117) * 10^40
        + 1336078311504491300376383412572050036595) * 10^40
        + 4716025427116221030518907688152282801837) * 10^40
        + 2581678080169853783093253651698199803047) : ℚ) /
        (((((((584860751115640981060573241432 * 10^40
        + 450911390469423409103523226034214575791) * 10^40
        + 9346282553121941065801670292732503914995) * 10^40
        + 832015092548368608753274700018866228220) * 10^40
        + 3707104606689189038890067409970169172066) * 10^40
        + 669759441489127340714707051750513966288) * 10^40
        + 5205680138673778664766888932849793792538) * 10^40
        + 4946258601787773726749188685340547743744)),
    (((-((((3198 * 10^40
        + 5767930144395324313296039490949183005330) * 10^40
        + 6285883584938857164191265785155455456742) * 10^40
        + 6485325796487709115522779725264306380283) * 10^40
        + 1485112308291401246528556190340323183249)) : ℚ) /
        (((229428567533355985723833127156833899 * 10^40
        + 5419281002131884419118444048418724328448) * 10^40
        + 7413844717706018872616230022222328717730) * 10^40
        + 698136352025966507310987301978860683264)))

noncomputable def batchC02704MinusMidpointP018Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP018BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP018Center2654‖ ≤
          batchC02704MinusMidpointP018Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP018Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP018Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP018Input2654 14 =
      (batchC02704MinusMidpointP018Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP018Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP018Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP018Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP018Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP018Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP018Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP018DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP018Factor2654 * embedPair2542
          batchC02704MinusMidpointP018Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP018Factor2654 : ℝ) *
            batchC02704MinusMidpointP018Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP018Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP018Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP018BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP018Factor2654)

def batchC02704MinusMidpointP019Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((118012873178861975857461921 : ℚ) /
        11805916207174113034240000000))

def batchC02704MinusMidpointP019Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP019Factor2654 : RatPair2542 := (((((((((((114 * 10^40
        + 6835716369766296211181381895088823632609) * 10^40
        + 9937509251232343744786605215677841874953) * 10^40
        + 9896174890900966696980311593208329022706) * 10^40
        + 8931369354022941391599861006799614715354) * 10^40
        + 8067161250813488193292437271050781911381) * 10^40
        + 5740290470264811879439424973364440265186) * 10^40
        + 2124702557355434049869094881569971671170) * 10^40
        + 2798743639236904351259025663068516241911) : ℚ) /
        (((((((584860751115640981060573241432 * 10^40
        + 450911390469423409103523226034214575791) * 10^40
        + 9346282553121941065801670292732503914995) * 10^40
        + 832015092548368608753274700018866228220) * 10^40
        + 3707104606689189038890067409970169172066) * 10^40
        + 669759441489127340714707051750513966288) * 10^40
        + 5205680138673778664766888932849793792538) * 10^40
        + 4946258601787773726749188685340547743744)),
    (((-((((1134 * 10^40
        + 6634202696439533876919840068983985619334) * 10^40
        + 2214316946235356328858900074312371030260) * 10^40
        + 9480340438098113416435035632806213854666) * 10^40
        + 8194824582254492353709920477608096113405)) : ℚ) /
        (((76476189177785328574611042385611299 * 10^40
        + 8473093667377294806372814682806241442816) * 10^40
        + 2471281572568672957538743340740776239243) * 10^40
        + 3566045450675322169103662433992953561088)))

noncomputable def batchC02704MinusMidpointP019Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP019BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP019Center2654‖ ≤
          batchC02704MinusMidpointP019Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP019Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP019Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP019Input2654 14 =
      (batchC02704MinusMidpointP019Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP019Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP019Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP019Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP019Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP019Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP019Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP019DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP019Factor2654 * embedPair2542
          batchC02704MinusMidpointP019Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP019Factor2654 : ℝ) *
            batchC02704MinusMidpointP019Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP019Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP019Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP019BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP019Factor2654)

def batchC02704MinusMidpointP020Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((2515138169851860170732905189 : ℚ) /
        236118324143482260684800000000))

def batchC02704MinusMidpointP020Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP020Factor2654 : RatPair2542 := (((((((((((1834 * 10^40
        + 9371458357276187869767242533751980161472) * 10^40
        + 9225299735247217811477421136050483676818) * 10^40
        + 4437325595680637689293553358828040202624) * 10^40
        + 8076564092587281753491671286901075022155) * 10^40
        + 5917276135684684748798937954840551738493) * 10^40
        + 9402480712374116359452135415602537850109) * 10^40
        + 8250747448435736659497971318039989431847) * 10^40
        + 219356294527228522631683017008468566135) : ℚ) /
        (((((((9357772017850255696969171862912 * 10^40
        + 7214582247510774545656371616547433212670) * 10^40
        + 9540520849951057052826724683720062639921) * 10^40
        + 3312241480773897740052395200301859651525) * 10^40
        + 9313673707027024622241078559522706753057) * 10^40
        + 716151063826037451435312828008223460616) * 10^40
        + 3290882218780458636270222925596700680615) * 10^40
        + 9140137628604379627987018965448763899904)),
    (((-((((14509 * 10^40
        + 4439346266809531197371828396592142240121) * 10^40
        + 379822022880251964558234036720494506105) * 10^40
        + 891781884347527109006090868768601360332) * 10^40
        + 8984741540484458894587889882249997228087)) : ℚ) /
        (((917714270133423942895332508627335598 * 10^40
        + 1677124008527537676473776193674897313794) * 10^40
        + 9655378870824075490464920088889314870920) * 10^40
        + 2792545408103866029243949207915442733056)))

noncomputable def batchC02704MinusMidpointP020Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP020BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP020Center2654‖ ≤
          batchC02704MinusMidpointP020Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP020Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP020Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP020Input2654 14 =
      (batchC02704MinusMidpointP020Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP020Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP020Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP020Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP020Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP020Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP020Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP020DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP020Factor2654 * embedPair2542
          batchC02704MinusMidpointP020Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP020Factor2654 : ℝ) *
            batchC02704MinusMidpointP020Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP020Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP020Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP020BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP020Factor2654)

def batchC02704MinusMidpointP021Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((2644392173593296965023470597 : ℚ) /
        236118324143482260684800000000))

def batchC02704MinusMidpointP021Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP021Factor2654 : RatPair2542 := (((((((((((1834 * 10^40
        + 9371455214068385013202701458634197584718) * 10^40
        + 8460348962981537670950100610411292047362) * 10^40
        + 6144485535663773421397841211242299755556) * 10^40
        + 5392142519998219718824763425304533617109) * 10^40
        + 8893591495496679084159290069318518157329) * 10^40
        + 5076186121755993756195906014866066454610) * 10^40
        + 426310026294041057136721803818713113280) * 10^40
        + 2716880981901957276264893262051365068087) : ℚ) /
        (((((((9357772017850255696969171862912 * 10^40
        + 7214582247510774545656371616547433212670) * 10^40
        + 9540520849951057052826724683720062639921) * 10^40
        + 3312241480773897740052395200301859651525) * 10^40
        + 9313673707027024622241078559522706753057) * 10^40
        + 716151063826037451435312828008223460616) * 10^40
        + 3290882218780458636270222925596700680615) * 10^40
        + 9140137628604379627987018965448763899904)),
    (((-((((5085 * 10^40
        + 301113778591227512142273262504458246117) * 10^40
        + 8935424135772420604682856441795748232831) * 10^40
        + 9034434793943743187483155261476564215611) * 10^40
        + 9225841088032970015970435306626576349917)) : ℚ) /
        (((305904756711141314298444169542445199 * 10^40
        + 3892374669509179225491258731224965771264) * 10^40
        + 9885126290274691830154973362963104956973) * 10^40
        + 4264181802701288676414649735971814244352)))

noncomputable def batchC02704MinusMidpointP021Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP021BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP021Center2654‖ ≤
          batchC02704MinusMidpointP021Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP021Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP021Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP021Input2654 14 =
      (batchC02704MinusMidpointP021Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP021Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP021Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP021Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP021Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP021Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP021Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP021DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP021Factor2654 * embedPair2542
          batchC02704MinusMidpointP021Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP021Factor2654 : ℝ) *
            batchC02704MinusMidpointP021Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP021Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP021Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP021BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP021Factor2654)

def batchC02704MinusMidpointP022Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((542109827843102595143241623 : ℚ) /
        47223664828696452136960000000))

def batchC02704MinusMidpointP022Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP022Factor2654 : RatPair2542 := (((((((((((1834 * 10^40
        + 9371453544326999626222791103170366952688) * 10^40
        + 3737758941589688540002888070794144082197) * 10^40
        + 8938991330752234356530164063070521331272) * 10^40
        + 1643731779473337826346523018311913568803) * 10^40
        + 82409412921854623270062169171622729729) * 10^40
        + 2144785396670083959316096728862019790242) * 10^40
        + 2571945748825740644376471632050712713723) * 10^40
        + 7754664898131800937332184234990348899751) : ℚ) /
        (((((((9357772017850255696969171862912 * 10^40
        + 7214582247510774545656371616547433212670) * 10^40
        + 9540520849951057052826724683720062639921) * 10^40
        + 3312241480773897740052395200301859651525) * 10^40
        + 9313673707027024622241078559522706753057) * 10^40
        + 716151063826037451435312828008223460616) * 10^40
        + 3290882218780458636270222925596700680615) * 10^40
        + 9140137628604379627987018965448763899904)),
    (((-((((15636 * 10^40
        + 7396586464749670477090323851931132036510) * 10^40
        + 9215702008833884929438386364038922332075) * 10^40
        + 303681220814811410372075008073527060786) * 10^40
        + 1011369635728095164090476313704858582545)) : ℚ) /
        (((917714270133423942895332508627335598 * 10^40
        + 1677124008527537676473776193674897313794) * 10^40
        + 9655378870824075490464920088889314870920) * 10^40
        + 2792545408103866029243949207915442733056)))

noncomputable def batchC02704MinusMidpointP022Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP022BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP022Center2654‖ ≤
          batchC02704MinusMidpointP022Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP022Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP022Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP022Input2654 14 =
      (batchC02704MinusMidpointP022Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP022Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP022Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP022Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP022Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP022Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP022Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP022DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP022Factor2654 * embedPair2542
          batchC02704MinusMidpointP022Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP022Factor2654 : ℝ) *
            batchC02704MinusMidpointP022Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP022Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP022Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP022BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP022Factor2654)

def batchC02704MinusMidpointP023Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((1450645982266156471694092723 : ℚ) /
        118059162071741130342400000000))

def batchC02704MinusMidpointP023Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP023Factor2654 : RatPair2542 := (((((((((((458 * 10^40
        + 7342862124798860796006268044347459295924) * 10^40
        + 8087079492939522595875626772090373954193) * 10^40
        + 5246750512074800022340194559448044371422) * 10^40
        + 1239240695827019960313973608208982450218) * 10^40
        + 7770736025646783956342878618102081551917) * 10^40
        + 6808730631813108546722362066801412755868) * 10^40
        + 8604020514602407960782018284867636540407) * 10^40
        + 5417671589734780422500557844291067748135) : ℚ) /
        (((((((2339443004462563924242292965728 * 10^40
        + 1803645561877693636414092904136858303167) * 10^40
        + 7385130212487764263206681170930015659980) * 10^40
        + 3328060370193474435013098800075464912881) * 10^40
        + 4828418426756756155560269639880676688264) * 10^40
        + 2679037765956509362858828207002055865154) * 10^40
        + 822720554695114659067555731399175170153) * 10^40
        + 9785034407151094906996754741362190974976)),
    (((-((((8368 * 10^40
        + 5527900528676641465269506197637451347139) * 10^40
        + 8085582207061165154043200020640960623040) * 10^40
        + 3875761109352403623177534459709198184249) * 10^40
        + 6671413524810976291466094645691624617809)) : ℚ) /
        (((458857135066711971447666254313667799 * 10^40
        + 838562004263768838236888096837448656897) * 10^40
        + 4827689435412037745232460044444657435460) * 10^40
        + 1396272704051933014621974603957721366528)))

noncomputable def batchC02704MinusMidpointP023Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP023BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP023Center2654‖ ≤
          batchC02704MinusMidpointP023Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP023Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP023Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP023Input2654 14 =
      (batchC02704MinusMidpointP023Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP023Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP023Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP023Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP023Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP023Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP023Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP023DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP023Factor2654 * embedPair2542
          batchC02704MinusMidpointP023Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP023Factor2654 : ℝ) *
            batchC02704MinusMidpointP023Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP023Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP023Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP023BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP023Factor2654)

def batchC02704MinusMidpointP024Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((1494474821378949476104378157 : ℚ) /
        118059162071741130342400000000))

def batchC02704MinusMidpointP024Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP024Factor2654 : RatPair2542 := (((((((((((458 * 10^40
        + 7342861516408955184984062126146886122427) * 10^40
        + 2089282259744716427120269201335312310444) * 10^40
        + 7467062209763840833286868473405206037219) * 10^40
        + 1776408024338266327623703461303161243873) * 10^40
        + 1524799936562582656807876130480935750882) * 10^40
        + 1285201046587515285306504122787232861623) * 10^40
        + 1362023263304925236756441638254334863092) * 10^40
        + 8395751140802177870497890961550708723815) : ℚ) /
        (((((((2339443004462563924242292965728 * 10^40
        + 1803645561877693636414092904136858303167) * 10^40
        + 7385130212487764263206681170930015659980) * 10^40
        + 3328060370193474435013098800075464912881) * 10^40
        + 4828418426756756155560269639880676688264) * 10^40
        + 2679037765956509362858828207002055865154) * 10^40
        + 822720554695114659067555731399175170153) * 10^40
        + 9785034407151094906996754741362190974976)),
    (((-((((8621 * 10^40
        + 3945986857107022171713161781139107513052) * 10^40
        + 2287531009867785291036532656938555695073) * 10^40
        + 1961117327430180408566894265488231230871) * 10^40
        + 2207432053183442604383844501868108273231)) : ℚ) /
        (((458857135066711971447666254313667799 * 10^40
        + 838562004263768838236888096837448656897) * 10^40
        + 4827689435412037745232460044444657435460) * 10^40
        + 1396272704051933014621974603957721366528)))

noncomputable def batchC02704MinusMidpointP024Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP024BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP024Center2654‖ ≤
          batchC02704MinusMidpointP024Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP024Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP024Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP024Input2654 14 =
      (batchC02704MinusMidpointP024Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP024Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP024Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP024Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP024Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP024Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP024Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP024DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP024Factor2654 * embedPair2542
          batchC02704MinusMidpointP024Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP024Factor2654 : ℝ) *
            batchC02704MinusMidpointP024Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP024Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP024Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP024BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP024Factor2654)

def batchC02704MinusMidpointP025Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((48419629474968996879914223 : ℚ) /
        3689348814741910323200000000))

def batchC02704MinusMidpointP025Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP025Factor2654 : RatPair2542 :=
    ((((((((((4479827012429701464007644318468603483092
    * 10^40
        + 5510669331310010988903301713008576227498) * 10^40
        + 3823072567538087463535313017577025217562) * 10^40
        + 8510009275810453475236413923216435346851) * 10^40
        + 4840562799025657758216209996520855149325) * 10^40
        + 3538529638307888418883239616376131523990) * 10^40
        + 3517275024009885307467506461645197856558) * 10^40
        + 7617993579793752002017363153689235664047) : ℚ) /
        (((((((2284612309045472582267864224 * 10^40
        + 3439261372619021185191810637601696150686) * 10^40
        + 6872446416223132582288287774580986343417) * 10^40
        + 9495437558955267064877942479296948696203) * 10^40
        + 9858230877369879644683164325820195973328) * 10^40
        + 3830741247818316903674666824420900445180) * 10^40
        + 8145334688041694447909245659893944507002) * 10^40
        + 1034946322663233491120114018302111514624)),
    (((-((((3 * 10^40
        + 2106364336167113791705545191213257597256) * 10^40
        + 8828995651770670656476241785472996067651) * 10^40
        + 3234837446418998714344253524041535735493) * 10^40
        + 1628608543955618823133650120135849939107)) : ℚ) /
        (((164819373227985621928041039624162 * 10^40
        + 2841536839800382100875803479919841037592) * 10^40
        + 2763946727527087657236074877889527534998) * 10^40
        + 3693030270367834746054102720762915848192)))

noncomputable def batchC02704MinusMidpointP025Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP025BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP025Center2654‖ ≤
          batchC02704MinusMidpointP025Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP025Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP025Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP025Input2654 14 =
      (batchC02704MinusMidpointP025Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP025Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP025Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP025Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP025Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP025Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP025Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP025DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP025Factor2654 * embedPair2542
          batchC02704MinusMidpointP025Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP025Factor2654 : ℝ) *
            batchC02704MinusMidpointP025Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP025Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP025Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP025BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP025Factor2654)

def batchC02704MinusMidpointP026Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((100349262824676998784528147 : ℚ) /
        7378697629483820646400000000))

def batchC02704MinusMidpointP026Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP026Factor2654 : RatPair2542 := (((((((((((1 * 10^40
        + 7919308046456624167028063572621927057743) * 10^40
        + 7234665686529232133503020615480445657731) * 10^40
        + 9271985575334975331899591679272188376202) * 10^40
        + 5877855627094790785415263822147841953909) * 10^40
        + 1745073885758067851253433657010993063541) * 10^40
        + 1112050765478241949583110940649378169892) * 10^40
        + 9519081545003485516106969829408668843464) * 10^40
        + 8803015063811322885544761801175852706535) : ℚ) /
        (((((((9138449236181890329071456897 * 10^40
        + 3757045490476084740767242550406784602746) * 10^40
        + 7489785664892530329153151098323945373671) * 10^40
        + 7981750235821068259511769917187794784815) * 10^40
        + 9432923509479518578732657303280783893313) * 10^40
        + 5322964991273267614698667297683601780723) * 10^40
        + 2581338752166777791636982639575778028008) * 10^40
        + 4139785290652933964480456073208446058496)),
    (((-((((192 * 10^40
        + 9664700318135891211216419403620690653924) * 10^40
        + 5822284538290518125789028678621905325049) * 10^40
        + 5684092188704850778573379223190110820061) * 10^40
        + 3761002722806413218716362697206111385467)) : ℚ) /
        (((9559523647223166071826380298201412 * 10^40
        + 4809136708422161850796601835350780180352) * 10^40
        + 308910196571084119692342917592597029905) * 10^40
        + 4195755681334415271137957804249119195136)))

noncomputable def batchC02704MinusMidpointP026Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP026BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP026Center2654‖ ≤
          batchC02704MinusMidpointP026Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP026Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP026Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP026Input2654 14 =
      (batchC02704MinusMidpointP026Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP026Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP026Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP026Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP026Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP026Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP026Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP026DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP026Factor2654 * embedPair2542
          batchC02704MinusMidpointP026Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP026Factor2654 : ℝ) *
            batchC02704MinusMidpointP026Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP026Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP026Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP026BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP026Factor2654)

def batchC02704MinusMidpointP027Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((210828625664342681326447037 : ℚ) /
        14757395258967641292800000000))

def batchC02704MinusMidpointP027Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP027Factor2654 : RatPair2542 := (((((((((((7 * 10^40
        + 1677232166177917748916212937820585529616) * 10^40
        + 1808650408724698383228553131463061795105) * 10^40
        + 2893203170225215106577990943314003660563) * 10^40
        + 6107607590936387273447774984713275437888) * 10^40
        + 2989723026343686184011262094830254975607) * 10^40
        + 8865672580795657349156591238537621076037) * 10^40
        + 4629545034564684715923242643478859411510) * 10^40
        + 5852174251827564501463002324938706037447) : ℚ) /
        (((((((36553796944727561316285827589 * 10^40
        + 5028181961904338963068970201627138410986) * 10^40
        + 9959142659570121316612604393295781494687) * 10^40
        + 1927000943284273038047079668751179139263) * 10^40
        + 7731694037918074314930629213123135573254) * 10^40
        + 1291859965093070458794669190734407122893) * 10^40
        + 325355008667111166547930558303112112033) * 10^40
        + 6559141162611735857921824292833784233984)),
    (((-((((1216 * 10^40
        + 2378037749509333497070589180807378635267) * 10^40
        + 6927096649349156042032641716909889872445) * 10^40
        + 2638438281360375867521702732572285814376) * 10^40
        + 7274954170963202968031518857986446598271)) : ℚ) /
        (((57357141883338996430958281789208474 * 10^40
        + 8854820250532971104779611012104681082112) * 10^40
        + 1853461179426504718154057505555582179432) * 10^40
        + 5174534088006491626827746825494715170816)))

noncomputable def batchC02704MinusMidpointP027Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP027BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP027Center2654‖ ≤
          batchC02704MinusMidpointP027Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP027Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP027Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP027Input2654 14 =
      (batchC02704MinusMidpointP027Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP027Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP027Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP027Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP027Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP027Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP027Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP027DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP027Factor2654 * embedPair2542
          batchC02704MinusMidpointP027Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP027Factor2654 : ℝ) *
            batchC02704MinusMidpointP027Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP027Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP027Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP027BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP027Factor2654)

def batchC02704MinusMidpointP028Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((859357086522682157795940137 : ℚ) /
        59029581035870565171200000000))

def batchC02704MinusMidpointP028Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP028Factor2654 : RatPair2542 := (((((((((((114 * 10^40
        + 6835714530103535390358969313776372981590) * 10^40
        + 739127688383602193607417090934224928387) * 10^40
        + 308871847149644771814124164214377604852) * 10^40
        + 9103459701677103234893154215492863716443) * 10^40
        + 6318094934470914518115559054569530587097) * 10^40
        + 584611198940995054677833249980839926140) * 10^40
        + 2357455312986773626189691981059847055401) * 10^40
        + 9783991876704295417783742186876766247487) : ℚ) /
        (((((((584860751115640981060573241432 * 10^40
        + 450911390469423409103523226034214575791) * 10^40
        + 9346282553121941065801670292732503914995) * 10^40
        + 832015092548368608753274700018866228220) * 10^40
        + 3707104606689189038890067409970169172066) * 10^40
        + 669759441489127340714707051750513966288) * 10^40
        + 5205680138673778664766888932849793792538) * 10^40
        + 4946258601787773726749188685340547743744)),
    (((-((((450 * 10^40
        + 6816732298824352743389230546015591628742) * 10^40
        + 4160029583486190248158432848097141861235) * 10^40
        + 1662593767405761146956676889242211841749) * 10^40
        + 4424268412052442830399483658317516725961)) : ℚ) /
        (((20857142503032362338530284286984899 * 10^40
        + 9583571000193807674465313095310793120768) * 10^40
        + 673985883427819897510566365656575337975) * 10^40
        + 4608921486547815137028271572907169153024)))

noncomputable def batchC02704MinusMidpointP028Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP028BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP028Center2654‖ ≤
          batchC02704MinusMidpointP028Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP028Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP028Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP028Input2654 14 =
      (batchC02704MinusMidpointP028Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP028Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP028Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP028Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP028Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP028Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP028Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP028DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP028Factor2654 * embedPair2542
          batchC02704MinusMidpointP028Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP028Factor2654 : ℝ) *
            batchC02704MinusMidpointP028Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP028Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP028Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP028BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP028Factor2654)

def batchC02704MinusMidpointP029Input2654 : RatPair2542 := ((((-((770791 * 10^40
        + 247585043534295989146970288614985069312) * 10^40
        + 7475057142589201517743210138031830463707)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((883780890450854350804880629 : ℚ) /
        59029581035870565171200000000))

def batchC02704MinusMidpointP029Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704MinusMidpointP029Factor2654 : RatPair2542 := (((((((((((114 * 10^40
        + 6835714329442066046586147678739599614502) * 10^40
        + 2245531265938184683276846938073587243957) * 10^40
        + 1244392930191070765810394488013127215682) * 10^40
        + 7548588552362747926919127641275125245559) * 10^40
        + 6769207494242833426954143749847417053108) * 10^40
        + 1101837771411102871139141540310229042311) * 10^40
        + 4337415351115621766596171219413979394828) * 10^40
        + 3457678885111230580890819380245497794775) : ℚ) /
        (((((((584860751115640981060573241432 * 10^40
        + 450911390469423409103523226034214575791) * 10^40
        + 9346282553121941065801670292732503914995) * 10^40
        + 832015092548368608753274700018866228220) * 10^40
        + 3707104606689189038890067409970169172066) * 10^40
        + 669759441489127340714707051750513966288) * 10^40
        + 5205680138673778664766888932849793792538) * 10^40
        + 4946258601787773726749188685340547743744)),
    (((-((((175 * 10^40
        + 8067434829879618176448625829156637476012) * 10^40
        + 5267227706020892271138831738724371513288) * 10^40
        + 6212524134339667222278382849489843386719) * 10^40
        + 1511097822437183082301289342955285692883)) : ℚ) /
        (((7911329914943309852545969901959789 * 10^40
        + 6393768310418340842038567036152369804429) * 10^40
        + 2669442921300207547331594138697321679921) * 10^40
        + 7265452977656067810596930596619960713216)))

noncomputable def batchC02704MinusMidpointP029Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704MinusMidpointP029BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP029Center2654‖ ≤
          batchC02704MinusMidpointP029Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704MinusMidpointP029Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704MinusMidpointP029Input2654]
  have hs : compactExp2547 batchC02704MinusMidpointP029Input2654 14 =
      (batchC02704MinusMidpointP029Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704MinusMidpointP029Input2654 14).2 : ℝ) =
      batchC02704MinusMidpointP029Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704MinusMidpointP029Error2654]
  have h := compactExp_error2547 batchC02704MinusMidpointP029Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      batchC02704MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704MinusMidpointP029Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704MinusMidpointP029Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704MinusMidpointP029DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP029Factor2654 * embedPair2542
          batchC02704MinusMidpointP029Center2654‖ ≤
        (pairMagnitude2542 batchC02704MinusMidpointP029Factor2654 : ℝ) *
            batchC02704MinusMidpointP029Error2654 := by
  have hx : |batchC02704MinusMidpointPosition2654| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC02704MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchC02704MinusMidpointPosition2654 = embedPair2542
          batchC02704MinusMidpointP029Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704MinusMidpointP029Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704MinusMidpointP029BaseError2654
    (embedPair_magnitude2542 batchC02704MinusMidpointP029Factor2654)

theorem batchC02704MinusMidpointGrid2654 :
    -stripRadius2303 + ((5409 : ℝ) /
        2) * (2 * stripRadius2303 / 10240) =
      batchC02704MinusMidpointPosition2654 := by
  norm_num [stripRadius2303, batchC02704MinusMidpointPosition2654]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP000DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP001DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP002DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP003DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP004DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP005DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP006DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP007DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP008DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP009DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP010DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP011DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP012DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP013DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP014DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP015DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP016DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP017DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP018DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP019DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP020DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP021DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP022DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP023DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP024DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP025DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP026DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP027DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP028DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointP029DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusMidpointGrid2654
