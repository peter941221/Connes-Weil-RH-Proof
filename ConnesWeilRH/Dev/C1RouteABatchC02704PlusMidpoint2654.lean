import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchC02704PlusMidpointPosition2654 : ℝ := (((-316604420831) : ℝ) /
        102400000000)

theorem batchC02704PlusMidpointZero2654 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchC02704PlusMidpointP000Center2654 : RatPair2542 := (0, 0)

def batchC02704PlusMidpointP000Factor2654 : RatPair2542 := (0, 0)

noncomputable def batchC02704PlusMidpointP000Error2654 : ℝ := 0

theorem batchC02704PlusMidpointP000Exterior2654 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02704PlusMidpointPosition2654 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |batchC02704PlusMidpointPosition2654| := by
    norm_num [storedWidth, batchC02704PlusMidpointPosition2654]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem batchC02704PlusMidpointP000BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP000Center2654‖ ≤ batchC02704PlusMidpointP000Error2654
          := by
  rw [batchC02704PlusMidpointP000Exterior2654]
  norm_num [batchC02704PlusMidpointP000Center2654, batchC02704PlusMidpointP000Error2654,
      batchC02704PlusMidpointZero2654]

theorem batchC02704PlusMidpointP000DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP000Factor2654 * embedPair2542
          batchC02704PlusMidpointP000Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP000Factor2654 : ℝ) *
            batchC02704PlusMidpointP000Error2654 := by
  rw [batchC02704PlusMidpointP000Exterior2654]
  norm_num [batchC02704PlusMidpointP000Factor2654, batchC02704PlusMidpointP000Center2654,
      batchC02704PlusMidpointP000Error2654,
      batchC02704PlusMidpointZero2654, pairMagnitude2542]

def batchC02704PlusMidpointP001Input2654 : RatPair2542 := ((((-((680 * 10^40
        + 3009416284252921996078528969456290627053) * 10^40
        + 2803423481834618406388332153398662201599)) : ℚ) /
        ((1911 * 10^40
        + 636059313002481026974552982466043868025) * 10^40
        + 9490129860940691830087093216870400000000)),
    ((1749014960699347497459862099 : ℚ) /
        7378697629483820646400000000))

def batchC02704PlusMidpointP001Center2654 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP001Factor2654 : RatPair2542 :=
    ((((((((((7428899423965724537940462875645 * 10^40
        + 2417783727513494690712035891377422547982) * 10^40
        + 8948076151341674490850649439899759756432) * 10^40
        + 267516282858513458413883651583759551474) * 10^40
        + 8555934161008766307391088226594845207775) * 10^40
        + 4057493123762885373091061859880930339586) * 10^40
        + 1814363082143161689279057760593941878500) * 10^40
        + 8060660708223920158211944196534584362455) : ℚ) /
        (((((((21853475072466884179775610 * 10^40
        + 5050691844828309978948358444045579402574) * 10^40
        + 5124429258150412373421189788125612843852) * 10^40
        + 3879206421653859396013998052716482817911) * 10^40
        + 5129388763405711352374537319737238752720) * 10^40
        + 7733405148124574933466135533777864478625) * 10^40
        + 4933855586968653219817805121510767357912) * 10^40
        + 4796348112336791170839587633781595439104)),
    (((-(((21571193320795640161434153877139294866 * 10^40
        + 3056639436186950672331725289338565851168) * 10^40
        + 8690103634257701397134815167791446506617) * 10^40
        + 3523884423021419537788303626899594557389)) : ℚ) /
        (((467477005557138437737010044212394 * 10^40
        + 6044292994922824666019867359004322520904) * 10^40
        + 5872892945262257961704847409476977725520) * 10^40
        + 8632871452613278619213937081947781070848)))

noncomputable def batchC02704PlusMidpointP001Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP001BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP001Center2654‖ ≤ batchC02704PlusMidpointP001Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP001Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP001Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP001Input2654 9 =
      (batchC02704PlusMidpointP001Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP001Input2654 9).2 : ℝ) =
      batchC02704PlusMidpointP001Error2654 := by
    rw [hs]
    norm_num [batchC02704PlusMidpointP001Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP001Input2654 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          batchC02704PlusMidpointP001Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP001Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP001DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP001Factor2654 * embedPair2542
          batchC02704PlusMidpointP001Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP001Factor2654 : ℝ) *
            batchC02704PlusMidpointP001Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP001Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP001Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP001BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP001Factor2654)

def batchC02704PlusMidpointP002Input2654 : RatPair2542 := ((((-((18068 * 10^40
        + 3250449009211160607530329309184626543483) * 10^40
        + 8211366392423118314858270267214288584959)) : ℚ) /
        ((73583 * 10^40
        + 7987996688174414725693033560276360199885) * 10^40
        + 3720647135657254640696745734963200000000)),
    (((-1749014960699347497459862099) : ℚ) /
        3689348814741910323200000000))

def batchC02704PlusMidpointP002Center2654 : RatPair2542 := ((((-292744349570841659209) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-335876800052985458825) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC02704PlusMidpointP002Factor2654 : RatPair2542 :=
    ((((((((((111838777870454128152010915416738295 *
    10^40
        + 3705351482032706990721004236438719430737) * 10^40
        + 97601548174450892350035869999762564353) * 10^40
        + 3143880010366048674724623122908637142873) * 10^40
        + 2264974578972384072455737269475372795902) * 10^40
        + 8905982929926963586607857033875500189947) * 10^40
        + 1296659487060541539353563818720297000653) * 10^40
        + 9432388825503897855635285168249049335255) : ℚ) /
        (((((((768544007996139530741708440094330 * 10^40
        + 9361303830205268585602265894693607351812) * 10^40
        + 824868157390208916240674428880399579936) * 10^40
        + 9148246831777139172358148600830896877111) * 10^40
        + 9608280519287181024184822336117609032452) * 10^40
        + 9688365701619582451736214667915733094333) * 10^40
        + 3844663304948024323402919916110603427146) * 10^40
        + 334390143674563506184767510638697119744)),
    (((((9118855474320520155043753470095428215496 * 10^40
        + 3125114389046306193573984748359673315764) * 10^40
        + 9378545500140908855224596255145558992720) * 10^40
        + 6715499105655737134984430910154849269709) : ℚ) /
        (((2772262628244552754429238432031480309 * 10^40
        + 6223291736604392270002797445474580939063) * 10^40
        + 4032601404758650854844934471541382160839) * 10^40
        + 1300403566374860875657492978631954137088)))

noncomputable def batchC02704PlusMidpointP002Error2654 : ℝ := ((695692910809332773 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchC02704PlusMidpointP002BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP002Center2654‖ ≤ batchC02704PlusMidpointP002Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP002Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP002Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP002Input2654 8 =
      (batchC02704PlusMidpointP002Center2654, ((695692910809332773 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP002Input2654 8).2 : ℝ) =
      batchC02704PlusMidpointP002Error2654 := by
    rw [hs]
    norm_num [batchC02704PlusMidpointP002Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP002Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02704PlusMidpointP002Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP002Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP002DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP002Factor2654 * embedPair2542
          batchC02704PlusMidpointP002Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP002Factor2654 : ℝ) *
            batchC02704PlusMidpointP002Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP002Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP002Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP002BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP002Factor2654)

def batchC02704PlusMidpointP003Input2654 : RatPair2542 := ((((-((2408035 * 10^40
        + 1386483025379189864971173608771469187781) * 10^40
        + 749849623705833655179222803862700786293)) : ℚ) /
        ((13308535 * 10^40
        + 6751979202907900655116715595283540785903) * 10^40
        + 7472841032378766672788969383526400000000)),
    (((-1749014960699347497459862099) : ℚ) /
        3689348814741910323200000000))

def batchC02704PlusMidpointP003Center2654 : RatPair2542 := ((((-2231444764515317886652878919) : ℚ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-5120444019494369590419387819) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC02704PlusMidpointP003Factor2654 : RatPair2542 := ((((-((((((((329721 * 10^40
        + 1111640970048926896777548657872669516603) * 10^40
        + 5199017432642533206082859261746981923349) * 10^40
        + 7317939979050124251214750376989864777128) * 10^40
        + 864433293841998194461851528603344931276) * 10^40
        + 8480462090855593017159842022050084269756) * 10^40
        + 272781724558355866683298934264975587003) * 10^40
        + 7123120233511074313182951306003103832417) * 10^40
        + 5173932396911843513256420770071007914635)) : ℚ) /
        ((((((((246 * 10^40
        + 7074527023425321848589250821495694315660) * 10^40
        + 1943541606688444486744994553651445089582) * 10^40
        + 9277507691300147203663236851156754571218) * 10^40
        + 4380126023106546251271957854717067248722) * 10^40
        + 4508009094711631319335178304978877911432) * 10^40
        + 2920485279896244824999788538258271621089) * 10^40
        + 1337925979484472046894370151108796136978) * 10^40
        + 9984506444795610497114336896346291699712)),
    ((((((31531 * 10^40
        + 6557818775767780099107966438006184845513) * 10^40
        + 3436105875064151496139865867569765083098) * 10^40
        + 8141408410816791577372292799905155820175) * 10^40
        + 6941698546093911830587852548837835742383) : ℚ) /
        ((((27 * 10^40
        + 2051899112472213698474640440590205680089) * 10^40
        + 7970833192203484612734256613353969058935) * 10^40
        + 3927699987012224977035553582790784574541) * 10^40
        + 7976106969681169150836269207915442733056)))

noncomputable def batchC02704PlusMidpointP003Error2654 : ℝ := ((39769098767867348111226715 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP003BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP003Center2654‖ ≤ batchC02704PlusMidpointP003Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP003Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP003Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP003Input2654 8 =
      (batchC02704PlusMidpointP003Center2654, ((39769098767867348111226715 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP003Input2654 8).2 : ℝ) =
      batchC02704PlusMidpointP003Error2654 := by
    rw [hs]
    norm_num [batchC02704PlusMidpointP003Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP003Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02704PlusMidpointP003Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP003Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP003DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP003Factor2654 * embedPair2542
          batchC02704PlusMidpointP003Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP003Factor2654 : ℝ) *
            batchC02704PlusMidpointP003Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP003Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP003Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP003BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP003Factor2654)

def batchC02704PlusMidpointP004Input2654 : RatPair2542 := ((((-((42059 * 10^40
        + 9952596262115416330879435783479966493285) * 10^40
        + 3834635124782580798238140213503351084959)) : ℚ) /
        ((268279 * 10^40
        + 8980219141639860859523318093054262845938) * 10^40
        + 634976154003494640696745734963200000000)),
    ((1749014960699347497459862099 : ℚ) /
        3689348814741910323200000000))

def batchC02704PlusMidpointP004Center2654 : RatPair2542 := ((((-2167703646726108964548046962265) :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((4974178769926100241614253136629 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC02704PlusMidpointP004Factor2654 : RatPair2542 :=
    ((((-(((((((201964458738058199915067974712496706943 *
    10^40
        + 1784388328427970880363428627603932155788) * 10^40
        + 2641610535986631223725542852248133639599) * 10^40
        + 6718690570182241637854822273034887801938) * 10^40
        + 9490109815371189337281780320433364155412) * 10^40
        + 320516372446396422232426782576676305476) * 10^40
        + 8129702289983392009136375841074516108991) * 10^40
        + 804394563848668641849579577844700664745)) : ℚ) /
        (((((((135797711855174546482627411704474083 * 10^40
        + 1438932361118371236678249609145534498703) * 10^40
        + 3302699898076317607206904280069547593226) * 10^40
        + 2258701786778009398077322959449149630908) * 10^40
        + 8578896788391039550319641454524174194249) * 10^40
        + 3658190695994485095205099368695549884643) * 10^40
        + 9587944744639141328784841006591277057687) * 10^40
        + 4299101381236757914427967510638697119744)),
    (((-((((2 * 10^40
        + 2120891315515016418302505128380854016887) * 10^40
        + 5592732070908995422319729996597520693104) * 10^40
        + 2446937338774632187522149408157668900601) * 10^40
        + 9159380448391089155798528712889224269709)) : ℚ) /
        (((36850741085516115639482908674473160594 * 10^40
        + 2340907442513691956545070470149820779182) * 10^40
        + 2352016578379110011499844513941403404846) * 10^40
        + 9829185100112973732540692978631954137088)))

noncomputable def batchC02704PlusMidpointP004Error2654 : ℝ := ((18855403652160012475762046497 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP004BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP004Center2654‖ ≤ batchC02704PlusMidpointP004Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP004Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP004Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP004Input2654 8 =
      (batchC02704PlusMidpointP004Center2654, ((18855403652160012475762046497 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP004Input2654 8).2 : ℝ) =
      batchC02704PlusMidpointP004Error2654 := by
    rw [hs]
    norm_num [batchC02704PlusMidpointP004Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP004Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02704PlusMidpointP004Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP004Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP004DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP004Factor2654 * embedPair2542
          batchC02704PlusMidpointP004Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP004Factor2654 : ℝ) *
            batchC02704PlusMidpointP004Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP004Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP004Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP004BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP004Factor2654)

def batchC02704PlusMidpointP005Center2654 : RatPair2542 := (0, 0)

def batchC02704PlusMidpointP005Factor2654 : RatPair2542 := (0, 0)

noncomputable def batchC02704PlusMidpointP005Error2654 : ℝ := 0

theorem batchC02704PlusMidpointP005Exterior2654 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02704PlusMidpointPosition2654 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |batchC02704PlusMidpointPosition2654| := by
    norm_num [storedWidth, batchC02704PlusMidpointPosition2654]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem batchC02704PlusMidpointP005BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP005Center2654‖ ≤ batchC02704PlusMidpointP005Error2654
          := by
  rw [batchC02704PlusMidpointP005Exterior2654]
  norm_num [batchC02704PlusMidpointP005Center2654, batchC02704PlusMidpointP005Error2654,
      batchC02704PlusMidpointZero2654]

theorem batchC02704PlusMidpointP005DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP005Factor2654 * embedPair2542
          batchC02704PlusMidpointP005Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP005Factor2654 : ℝ) *
            batchC02704PlusMidpointP005Error2654 := by
  rw [batchC02704PlusMidpointP005Exterior2654]
  norm_num [batchC02704PlusMidpointP005Factor2654, batchC02704PlusMidpointP005Center2654,
      batchC02704PlusMidpointP005Error2654,
      batchC02704PlusMidpointZero2654, pairMagnitude2542]

def batchC02704PlusMidpointP006Input2654 : RatPair2542 :=
    ((((-350724550300130092278570586529094603) : ℚ) /
        590119355113074880408793907200000000),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP006Center2654 : RatPair2542 := (((1337454337557907 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP006Factor2654 : RatPair2542 := (((((155052713674800 * 10^40
        + 4268453122142098319767700819755151911034) * 10^40
        + 6892894643247701537329842547866493252883) : ℚ) /
        ((30816335580 * 10^40
        + 6749904453217039673672739966804559017622) * 10^40
        + 7356208886278486149319370191465973011532)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP006Error2654 : ℝ := ((2540060805751 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP006BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP006Center2654‖ ≤ batchC02704PlusMidpointP006Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP006Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP006Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP006Input2654 7 =
      (batchC02704PlusMidpointP006Center2654, ((2540060805751 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP006Input2654 7).2 : ℝ) =
      batchC02704PlusMidpointP006Error2654 := by
    rw [hs]
    norm_num [batchC02704PlusMidpointP006Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP006Input2654 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          batchC02704PlusMidpointP006Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP006Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP006DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP006Factor2654 * embedPair2542
          batchC02704PlusMidpointP006Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP006Factor2654 : ℝ) *
            batchC02704PlusMidpointP006Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP006Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP006Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP006BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP006Factor2654)

def batchC02704PlusMidpointP007Input2654 : RatPair2542 := ((((-((2408035 * 10^40
        + 1386483025379189864971173608771469187781) * 10^40
        + 749849623705833655179222803862700786293)) : ℚ) /
        ((3327133 * 10^40
        + 9187994800726975163779178898820885196475) * 10^40
        + 9368210258094691668197242345881600000000)),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP007Center2654 : RatPair2542 := (((11171086374002929260000775549 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP007Factor2654 : RatPair2542 := ((((((((((101771005533749310 * 10^40
        + 8557077042359700063014591621188413982728) * 10^40
        + 1186847099051438031661540222793328754406) * 10^40
        + 6233863199402730313493955902937083893752) * 10^40
        + 1783706805974828950990878920563404564654) * 10^40
        + 560450243758165192055631801360362285083) * 10^40
        + 5488113332490806514728554388271459044697) * 10^40
        + 7858700213291042998799386271766083175443) : ℚ) /
        (((((((498221733026662 * 10^40
        + 1058294087558394478251182740073524950865) * 10^40
        + 8781112511588950888454777901048648846762) * 10^40
        + 6142968013292857213882197233096918621030) * 10^40
        + 8554722893874301915232046889558267123534) * 10^40
        + 776304342128346830564005224693078678247) * 10^40
        + 6773636077192297067392725532071283799412) * 10^40
        + 5652528853164171995197545087064332701772)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP007Error2654 : ℝ := ((1621058578149108307779805 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP007BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP007Center2654‖ ≤ batchC02704PlusMidpointP007Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP007Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP007Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP007Input2654 6 =
      (batchC02704PlusMidpointP007Center2654, ((1621058578149108307779805 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP007Input2654 6).2 : ℝ) =
      batchC02704PlusMidpointP007Error2654 := by
    rw [hs]
    norm_num [batchC02704PlusMidpointP007Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP007Input2654 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          batchC02704PlusMidpointP007Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP007Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP007DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP007Factor2654 * embedPair2542
          batchC02704PlusMidpointP007Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP007Factor2654 : ℝ) *
            batchC02704PlusMidpointP007Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP007Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP007Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP007BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP007Factor2654)

def batchC02704PlusMidpointP008Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((782182 * 10^40
        + 5320360220295712195426977782364918186105) * 10^40
        + 7018763413979605529247020272844800000000)),
    ((1259633303355652447930297807 : ℚ) /
        236118324143482260684800000000))

def batchC02704PlusMidpointP008Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP008Factor2654 : RatPair2542 := (((((((((((22019 * 10^40
        + 2772365633617756001933851968099223759286) * 10^40
        + 3213935220971554162051937160217591351698) * 10^40
        + 779523803228191141080931439312912376910) * 10^40
        + 3405136799372660278842028336999675088109) * 10^40
        + 2544129493224329707773069360351408100132) * 10^40
        + 7554417579987556648653367201602997084764) * 10^40
        + 8000422361580059461634804709681425502153) * 10^40
        + 2078154214453545701579539489739496546125) : ℚ) /
        (((((((112293264214203068363630062354952 * 10^40
        + 6574986970129294547876459398569198552051) * 10^40
        + 4486250199412684633920696204640751679055) * 10^40
        + 9746897769286772880628742403622315818311) * 10^40
        + 1764084484324295466892942714272481036684) * 10^40
        + 8593812765912449417223753936098681527395) * 10^40
        + 9490586625365503635242675107160408167390) * 10^40
        + 9681651543252555535844227585385166798848)),
    (((-((((7266 * 10^40
        + 6353135142615756763727417538065324992567) * 10^40
        + 8839907945505512422076203957678271265138) * 10^40
        + 8338618024416357977755804560435709013416) * 10^40
        + 7751047959855009976523450351656348205819)) : ℚ) /
        (((1835428540266847885790665017254671196 * 10^40
        + 3354248017055075352947552387349794627589) * 10^40
        + 9310757741648150980929840177778629741840) * 10^40
        + 5585090816207732058487898415830885466112)))

noncomputable def batchC02704PlusMidpointP008Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP008BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP008Center2654‖ ≤ batchC02704PlusMidpointP008Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP008Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP008Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP008Input2654 13 =
      (batchC02704PlusMidpointP008Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP008Input2654 13).2 : ℝ) =
      batchC02704PlusMidpointP008Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP008Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP008Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchC02704PlusMidpointP008Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP008Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP008DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP008Factor2654 * embedPair2542
          batchC02704PlusMidpointP008Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP008Factor2654 : ℝ) *
            batchC02704PlusMidpointP008Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP008Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP008Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP008BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP008Factor2654)

def batchC02704PlusMidpointP009Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((782182 * 10^40
        + 5320360220295712195426977782364918186105) * 10^40
        + 7018763413979605529247020272844800000000)),
    ((1873404750918948301439333841 : ℚ) /
        236118324143482260684800000000))

def batchC02704PlusMidpointP009Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP009Factor2654 : RatPair2542 := (((((((((((22019 * 10^40
        + 2772338443410098389819427803412309146209) * 10^40
        + 7744835942337821668601357279752173059817) * 10^40
        + 5934683627603334873746326766792570266244) * 10^40
        + 4595744547816514169805182055522202609906) * 10^40
        + 8385304538856224668340305411709415413021) * 10^40
        + 6135439405305632414755013560450094919354) * 10^40
        + 5409277290786397403541399536270893596297) * 10^40
        + 722103860502875653549725022826724160909) : ℚ) /
        (((((((112293264214203068363630062354952 * 10^40
        + 6574986970129294547876459398569198552051) * 10^40
        + 4486250199412684633920696204640751679055) * 10^40
        + 9746897769286772880628742403622315818311) * 10^40
        + 1764084484324295466892942714272481036684) * 10^40
        + 8593812765912449417223753936098681527395) * 10^40
        + 9490586625365503635242675107160408167390) * 10^40
        + 9681651543252555535844227585385166798848)),
    (((-((((3602 * 10^40
        + 4635326453532922225827488870417161327987) * 10^40
        + 2173079221711396196710013796728106212365) * 10^40
        + 816904676725985470419315191281286381905) * 10^40
        + 7167905602451766714523698568464141430199)) : ℚ) /
        (((611809513422282628596888339084890398 * 10^40
        + 7784749339018358450982517462449931542529) * 10^40
        + 9770252580549383660309946725926209913946) * 10^40
        + 8528363605402577352829299471943628488704)))

noncomputable def batchC02704PlusMidpointP009Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP009BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP009Center2654‖ ≤ batchC02704PlusMidpointP009Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP009Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP009Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP009Input2654 13 =
      (batchC02704PlusMidpointP009Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP009Input2654 13).2 : ℝ) =
      batchC02704PlusMidpointP009Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP009Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP009Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchC02704PlusMidpointP009Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP009Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP009DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP009Factor2654 * embedPair2542
          batchC02704PlusMidpointP009Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP009Factor2654 : ℝ) *
            batchC02704PlusMidpointP009Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP009Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP009Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP009BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP009Factor2654)

def batchC02704PlusMidpointP010Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((782182 * 10^40
        + 5320360220295712195426977782364918186105) * 10^40
        + 7018763413979605529247020272844800000000)),
    ((1114436568009919590097554951 : ℚ) /
        118059162071741130342400000000))

def batchC02704PlusMidpointP010Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP010Factor2654 : RatPair2542 := (((((((((((5504 * 10^40
        + 8193079456118765092856975883596752604796) * 10^40
        + 2950533410385154878883598817800421795592) * 10^40
        + 1397219408933062970702420965326250215540) * 10^40
        + 2542893720335768042751185935695799134694) * 10^40
        + 6540925964691086353812605262178187317578) * 10^40
        + 6951365940587677922779254651610725211756) * 10^40
        + 584826419159391331169823512259026619440) * 10^40
        + 6379151360148188508177222958385378649565) : ℚ) /
        (((((((28073316053550767090907515588738 * 10^40
        + 1643746742532323636969114849642299638012) * 10^40
        + 8621562549853171158480174051160187919763) * 10^40
        + 9936724442321693220157185600905578954577) * 10^40
        + 7941021121081073866723235678568120259171) * 10^40
        + 2148453191478112354305938484024670381848) * 10^40
        + 9872646656341375908810668776790102041847) * 10^40
        + 7420412885813138883961056896346291699712)),
    (((-((((2143 * 10^40
        + 57192568060799629380786195352442617990) * 10^40
        + 2080926446915085097072048297338816184996) * 10^40
        + 4189146288580845108501407559433873087197) * 10^40
        + 8386762654605898800841658050399667037489)) : ℚ) /
        (((305904756711141314298444169542445199 * 10^40
        + 3892374669509179225491258731224965771264) * 10^40
        + 9885126290274691830154973362963104956973) * 10^40
        + 4264181802701288676414649735971814244352)))

noncomputable def batchC02704PlusMidpointP010Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP010BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP010Center2654‖ ≤ batchC02704PlusMidpointP010Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP010Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP010Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP010Input2654 13 =
      (batchC02704PlusMidpointP010Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP010Input2654 13).2 : ℝ) =
      batchC02704PlusMidpointP010Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP010Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP010Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchC02704PlusMidpointP010Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP010Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP010DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP010Factor2654 * embedPair2542
          batchC02704PlusMidpointP010Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP010Factor2654 : ℝ) *
            batchC02704PlusMidpointP010Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP010Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP010Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP010BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP010Factor2654)

def batchC02704PlusMidpointP011Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((782182 * 10^40
        + 5320360220295712195426977782364918186105) * 10^40
        + 7018763413979605529247020272844800000000)),
    ((1232937275700447526054176631 : ℚ) /
        118059162071741130342400000000))

def batchC02704PlusMidpointP011Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP011Factor2654 : RatPair2542 := (((((((((((5504 * 10^40
        + 8193075522942785952601428332673623900949) * 10^40
        + 4197240818699515269877071182245445940145) * 10^40
        + 2470097200493987529358367674697139272367) * 10^40
        + 2836230521289259992562842583723078930708) * 10^40
        + 304732981062036633294227771157317896712) * 10^40
        + 9684069508995624198194397182192234692128) * 10^40
        + 3819941921232217804850299124804806289514) * 10^40
        + 1354731533569432532998053982656222274685) : ℚ) /
        (((((((28073316053550767090907515588738 * 10^40
        + 1643746742532323636969114849642299638012) * 10^40
        + 8621562549853171158480174051160187919763) * 10^40
        + 9936724442321693220157185600905578954577) * 10^40
        + 7941021121081073866723235678568120259171) * 10^40
        + 2148453191478112354305938484024670381848) * 10^40
        + 9872646656341375908810668776790102041847) * 10^40
        + 7420412885813138883961056896346291699712)),
    (((-((((7112 * 10^40
        + 6299400670234736032933537428717175373582) * 10^40
        + 3728081191240284085105237527842347247952) * 10^40
        + 3698495322152973619805115408079631728887) * 10^40
        + 3984324321171201405880818139833526425027)) : ℚ) /
        (((917714270133423942895332508627335598 * 10^40
        + 1677124008527537676473776193674897313794) * 10^40
        + 9655378870824075490464920088889314870920) * 10^40
        + 2792545408103866029243949207915442733056)))

noncomputable def batchC02704PlusMidpointP011Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP011BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP011Center2654‖ ≤ batchC02704PlusMidpointP011Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP011Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP011Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP011Input2654 13 =
      (batchC02704PlusMidpointP011Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP011Input2654 13).2 : ℝ) =
      batchC02704PlusMidpointP011Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP011Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP011Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchC02704PlusMidpointP011Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP011Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP011DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP011Factor2654 * embedPair2542
          batchC02704PlusMidpointP011Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP011Factor2654 : ℝ) *
            batchC02704PlusMidpointP011Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP011Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP011Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP011BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP011Factor2654)

def batchC02704PlusMidpointP012Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((782182 * 10^40
        + 5320360220295712195426977782364918186105) * 10^40
        + 7018763413979605529247020272844800000000)),
    ((27113500145429484224061979 : ℚ) /
        2361183241434822606848000000))

def batchC02704PlusMidpointP012Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP012Factor2654 : RatPair2542 := (((((((((((1376 * 10^40
        + 2048267757617970171642753873796911822360) * 10^40
        + 1852595580265523574270969272552224245734) * 10^40
        + 8466327284166070817180797608896834773414) * 10^40
        + 4538536855868948837315046754432499269248) * 10^40
        + 5043608302200960144544453771836238715777) * 10^40
        + 3390380607734928778807639749699961045516) * 10^40
        + 6571643114673914235121940856442493669580) * 10^40
        + 3254347410417823744320692684423997054357) : ℚ) /
        (((((((7018329013387691772726878897184 * 10^40
        + 5410936685633080909242278712410574909503) * 10^40
        + 2155390637463292789620043512790046979940) * 10^40
        + 9984181110580423305039296400226394738644) * 10^40
        + 4485255280270268466680808919642030064792) * 10^40
        + 8037113297869528088576484621006167595462) * 10^40
        + 2468161664085343977202667194197525510461) * 10^40
        + 9355103221453284720990264224086572924928)),
    (((-((((3910 * 10^40
        + 3427383366633296174326588722177648812296) * 10^40
        + 3774626951457257476153878646953999674171) * 10^40
        + 5684132659010427704257414594830586976684) * 10^40
        + 2392415909292569059735885628314961108575)) : ℚ) /
        (((458857135066711971447666254313667799 * 10^40
        + 838562004263768838236888096837448656897) * 10^40
        + 4827689435412037745232460044444657435460) * 10^40
        + 1396272704051933014621974603957721366528)))

noncomputable def batchC02704PlusMidpointP012Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP012BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP012Center2654‖ ≤ batchC02704PlusMidpointP012Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP012Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP012Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP012Input2654 13 =
      (batchC02704PlusMidpointP012Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP012Input2654 13).2 : ℝ) =
      batchC02704PlusMidpointP012Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP012Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP012Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchC02704PlusMidpointP012Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP012Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP012DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP012Factor2654 * embedPair2542
          batchC02704PlusMidpointP012Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP012Factor2654 : ℝ) *
            batchC02704PlusMidpointP012Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP012Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP012Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP012BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP012Factor2654)

def batchC02704PlusMidpointP013Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((782182 * 10^40
        + 5320360220295712195426977782364918186105) * 10^40
        + 7018763413979605529247020272844800000000)),
    ((293504825937452683545508821 : ℚ) /
        23611832414348226068480000000))

def batchC02704PlusMidpointP013Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP013Factor2654 : RatPair2542 := (((((((((((5504 * 10^40
        + 8193066565545868288800824819181562174709) * 10^40
        + 2000168924616286951235668324322502556604) * 10^40
        + 4460816803708485849106719289102734237461) * 10^40
        + 6646967900285787994263516618329088396194) * 10^40
        + 3101326501344195076736894892050732437003) * 10^40
        + 3326809442343900969605078962783805990426) * 10^40
        + 2031262536550255068868531696829353977154) * 10^40
        + 5110182452297797395665022479438996657853) : ℚ) /
        (((((((28073316053550767090907515588738 * 10^40
        + 1643746742532323636969114849642299638012) * 10^40
        + 8621562549853171158480174051160187919763) * 10^40
        + 9936724442321693220157185600905578954577) * 10^40
        + 7941021121081073866723235678568120259171) * 10^40
        + 2148453191478112354305938484024670381848) * 10^40
        + 9872646656341375908810668776790102041847) * 10^40
        + 7420412885813138883961056896346291699712)),
    (((-((((2821 * 10^40
        + 9754208919492896656261157366764962324478) * 10^40
        + 9969854751327408635843767079865209015493) * 10^40
        + 9398785233141547895774340537628656355173) * 10^40
        + 4719908164101472407205334194125899832095)) : ℚ) /
        (((305904756711141314298444169542445199 * 10^40
        + 3892374669509179225491258731224965771264) * 10^40
        + 9885126290274691830154973362963104956973) * 10^40
        + 4264181802701288676414649735971814244352)))

noncomputable def batchC02704PlusMidpointP013Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP013BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP013Center2654‖ ≤ batchC02704PlusMidpointP013Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP013Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP013Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP013Input2654 13 =
      (batchC02704PlusMidpointP013Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP013Input2654 13).2 : ℝ) =
      batchC02704PlusMidpointP013Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP013Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP013Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchC02704PlusMidpointP013Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP013Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP013DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP013Factor2654 * embedPair2542
          batchC02704PlusMidpointP013Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP013Factor2654 : ℝ) *
            batchC02704PlusMidpointP013Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP013Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP013Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP013BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP013Factor2654)

def batchC02704PlusMidpointP014Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((782182 * 10^40
        + 5320360220295712195426977782364918186105) * 10^40
        + 7018763413979605529247020272844800000000)),
    ((1674769098088922039627248141 : ℚ) /
        118059162071741130342400000000))

def batchC02704PlusMidpointP014Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP014Factor2654 : RatPair2542 := (((((((((((5504 * 10^40
        + 8193057357427828568872132095010953194778) * 10^40
        + 4198836674020502424254257369567435932667) * 10^40
        + 5935252146787569619003618685230271119311) * 10^40
        + 3467739728275667118488817077692563490280) * 10^40
        + 4945170289382837268288081705171630111264) * 10^40
        + 7298285321070395277040800014534005956035) * 10^40
        + 7240824611845626820370616469194720240991) * 10^40
        + 2271140506075112229474820428283981742325) : ℚ) /
        (((((((28073316053550767090907515588738 * 10^40
        + 1643746742532323636969114849642299638012) * 10^40
        + 8621562549853171158480174051160187919763) * 10^40
        + 9936724442321693220157185600905578954577) * 10^40
        + 7941021121081073866723235678568120259171) * 10^40
        + 2148453191478112354305938484024670381848) * 10^40
        + 9872646656341375908810668776790102041847) * 10^40
        + 7420412885813138883961056896346291699712)),
    (((-((((9661 * 10^40
        + 4913544559229962396411938769398291979344) * 10^40
        + 3543975487402808784780708844304214609367) * 10^40
        + 9829924184985748570958443210475189479485) * 10^40
        + 9288494831194862991273611521782998023697)) : ℚ) /
        (((917714270133423942895332508627335598 * 10^40
        + 1677124008527537676473776193674897313794) * 10^40
        + 9655378870824075490464920088889314870920) * 10^40
        + 2792545408103866029243949207915442733056)))

noncomputable def batchC02704PlusMidpointP014Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP014BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP014Center2654‖ ≤ batchC02704PlusMidpointP014Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP014Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP014Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP014Input2654 13 =
      (batchC02704PlusMidpointP014Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP014Input2654 13).2 : ℝ) =
      batchC02704PlusMidpointP014Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP014Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP014Input2654 hz 13
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^13 * embedPair2542
          batchC02704PlusMidpointP014Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP014Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP014DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP014Factor2654 * embedPair2542
          batchC02704PlusMidpointP014Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP014Factor2654 : ℝ) *
            batchC02704PlusMidpointP014Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP014Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP014Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP014BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP014Factor2654)

def batchC02704PlusMidpointP015Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((1823260823309772955292476057 : ℚ) /
        236118324143482260684800000000))

def batchC02704PlusMidpointP015Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP015Factor2654 : RatPair2542 := (((((((((((5504 * 10^40
        + 8193050012865069445023270909351163364912) * 10^40
        + 4026824730509614003252891364291247740665) * 10^40
        + 8305625104402767000907299536122501881446) * 10^40
        + 6038617447329982959833688453104492121667) * 10^40
        + 3612529990896917938635289330661622409542) * 10^40
        + 4537908950064776355300964889500543458475) * 10^40
        + 9733032236166375711769391132868131669567) * 10^40
        + 2460504183458045689210147355065336717341) : ℚ) /
        (((((((28073316053550767090907515588738 * 10^40
        + 1643746742532323636969114849642299638012) * 10^40
        + 8621562549853171158480174051160187919763) * 10^40
        + 9936724442321693220157185600905578954577) * 10^40
        + 7941021121081073866723235678568120259171) * 10^40
        + 2148453191478112354305938484024670381848) * 10^40
        + 9872646656341375908810668776790102041847) * 10^40
        + 7420412885813138883961056896346291699712)),
    (((-((((10518 * 10^40
        + 1178118383619231805752862878884598680125) * 10^40
        + 4610742346001071851668663802164418035002) * 10^40
        + 8868330419336328812919723287463246847225) * 10^40
        + 2075013030787370958882163663783298461069)) : ℚ) /
        (((917714270133423942895332508627335598 * 10^40
        + 1677124008527537676473776193674897313794) * 10^40
        + 9655378870824075490464920088889314870920) * 10^40
        + 2792545408103866029243949207915442733056)))

noncomputable def batchC02704PlusMidpointP015Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP015BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP015Center2654‖ ≤ batchC02704PlusMidpointP015Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP015Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP015Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP015Input2654 14 =
      (batchC02704PlusMidpointP015Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP015Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP015Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP015Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP015Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP015Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP015Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP015DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP015Factor2654 * embedPair2542
          batchC02704PlusMidpointP015Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP015Factor2654 : ℝ) *
            batchC02704PlusMidpointP015Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP015Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP015Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP015BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP015Factor2654)

def batchC02704PlusMidpointP016Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((965286270060315490254887079 : ℚ) /
        118059162071741130342400000000))

def batchC02704PlusMidpointP016Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP016Factor2654 : RatPair2542 := (((((((((((1376 * 10^40
        + 2048261079241431307450387324248111316336) * 10^40
        + 9786616970419215306718515859467042437985) * 10^40
        + 3314548606147532691851345615488482707226) * 10^40
        + 9123322280737363425460158878162503835461) * 10^40
        + 8436006705730993218995970691727858528917) * 10^40
        + 3695235562697772715446718742649686671841) * 10^40
        + 8353400368949248642190201825685577128052) * 10^40
        + 725143309118984439124003337206969601949) : ℚ) /
        (((((((7018329013387691772726878897184 * 10^40
        + 5410936685633080909242278712410574909503) * 10^40
        + 2155390637463292789620043512790046979940) * 10^40
        + 9984181110580423305039296400226394738644) * 10^40
        + 4485255280270268466680808919642030064792) * 10^40
        + 8037113297869528088576484621006167595462) * 10^40
        + 2468161664085343977202667194197525510461) * 10^40
        + 9355103221453284720990264224086572924928)),
    (((-((((30 * 10^40
        + 4294617117055556769673396755860817420865) * 10^40
        + 3987607979903357118781336771497093797883) * 10^40
        + 5158534662558090460043433952305941526461) * 10^40
        + 7757892415474606384236109688838962728421)) : ℚ) /
        (((2507416038615912412282329258544632 * 10^40
        + 7818789956307452288733534907632991522715) * 10^40
        + 2867910871231759769099630929204615614401) * 10^40
        + 4215280178710666300626349587999768969216)))

noncomputable def batchC02704PlusMidpointP016Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP016BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP016Center2654‖ ≤ batchC02704PlusMidpointP016Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP016Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP016Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP016Input2654 14 =
      (batchC02704PlusMidpointP016Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP016Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP016Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP016Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP016Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP016Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP016Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP016DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP016Factor2654 * embedPair2542
          batchC02704PlusMidpointP016Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP016Factor2654 : ℝ) *
            batchC02704PlusMidpointP016Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP016Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP016Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP016BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP016Factor2654)

def batchC02704PlusMidpointP017Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((2139018841052257346363716437 : ℚ) /
        236118324143482260684800000000))

def batchC02704PlusMidpointP017Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP017Factor2654 : RatPair2542 := (((((((((((5504 * 10^40
        + 8193032322382267546271993700073961415349) * 10^40
        + 5078914570964594691988185015525554802987) * 10^40
        + 8536681072217129469840254106104598409685) * 10^40
        + 4292493474638673660822614882033252848453) * 10^40
        + 3244495194351099730057330184681587758775) * 10^40
        + 5527926479749516787224521201955588389461) * 10^40
        + 3468095298358308765387844273898520052217) * 10^40
        + 5839252070594665510141696535373113478981) : ℚ) /
        (((((((28073316053550767090907515588738 * 10^40
        + 1643746742532323636969114849642299638012) * 10^40
        + 8621562549853171158480174051160187919763) * 10^40
        + 9936724442321693220157185600905578954577) * 10^40
        + 7941021121081073866723235678568120259171) * 10^40
        + 2148453191478112354305938484024670381848) * 10^40
        + 9872646656341375908810668776790102041847) * 10^40
        + 7420412885813138883961056896346291699712)),
    (((-((((4113 * 10^40
        + 2261283912311440614100243579888438679377) * 10^40
        + 3014381020021106316750355145584021509880) * 10^40
        + 7815970198864244107122696140423499974224) * 10^40
        + 1029378838922605638251244967765657333843)) : ℚ) /
        (((305904756711141314298444169542445199 * 10^40
        + 3892374669509179225491258731224965771264) * 10^40
        + 9885126290274691830154973362963104956973) * 10^40
        + 4264181802701288676414649735971814244352)))

noncomputable def batchC02704PlusMidpointP017Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP017BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP017Center2654‖ ≤ batchC02704PlusMidpointP017Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP017Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP017Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP017Input2654 14 =
      (batchC02704PlusMidpointP017Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP017Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP017Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP017Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP017Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP017Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP017Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP017DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP017Factor2654 * embedPair2542
          batchC02704PlusMidpointP017Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP017Factor2654 : ℝ) *
            batchC02704PlusMidpointP017Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP017Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP017Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP017BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP017Factor2654)

def batchC02704PlusMidpointP018Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((554456987983803044582380403 : ℚ) /
        59029581035870565171200000000))

def batchC02704PlusMidpointP018Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP018Factor2654 : RatPair2542 := (((((((((((344 * 10^40
        + 512064216711632653659496859960808978756) * 10^40
        + 934280615113843303470177444825467337360) * 10^40
        + 6564881518541476437643573601176550930120) * 10^40
        + 1914590625786036962880846440074666308159) * 10^40
        + 6218205914813304861770820330734823123788) * 10^40
        + 4641635275303187414183196630310497938810) * 10^40
        + 2081130236053981860188473677708285848844) * 10^40
        + 7644449734182521349279760955094599409141) : ℚ) /
        (((((((1754582253346922943181719724296 * 10^40
        + 1352734171408270227310569678102643727375) * 10^40
        + 8038847659365823197405010878197511744985) * 10^40
        + 2496045277645105826259824100056598684661) * 10^40
        + 1121313820067567116670202229910507516198) * 10^40
        + 2009278324467382022144121155251541898865) * 10^40
        + 5617040416021335994300666798549381377615) * 10^40
        + 4838775805363321180247566056021643231232)),
    (((-((((3198 * 10^40
        + 5790769222567319487043279025022814718446) * 10^40
        + 9308053025540345348510899028408497948621) * 10^40
        + 4705676483499200759142569073682596478227) * 10^40
        + 9376910590847158753471443809659676816751)) : ℚ) /
        (((229428567533355985723833127156833899 * 10^40
        + 5419281002131884419118444048418724328448) * 10^40
        + 7413844717706018872616230022222328717730) * 10^40
        + 698136352025966507310987301978860683264)))

noncomputable def batchC02704PlusMidpointP018Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP018BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP018Center2654‖ ≤ batchC02704PlusMidpointP018Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP018Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP018Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP018Input2654 14 =
      (batchC02704PlusMidpointP018Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP018Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP018Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP018Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP018Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP018Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP018Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP018DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP018Factor2654 * embedPair2542
          batchC02704PlusMidpointP018Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP018Factor2654 : ℝ) *
            batchC02704PlusMidpointP018Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP018Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP018Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP018BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP018Factor2654)

def batchC02704PlusMidpointP019Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((118012873178861975857461921 : ℚ) /
        11805916207174113034240000000))

def batchC02704PlusMidpointP019Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP019Factor2654 : RatPair2542 := (((((((((((344 * 10^40
        + 512063640470750063047679115391410146335) * 10^40
        + 2668875345094707034483316394335004662106) * 10^40
        + 6283337082143177365994567908368378062791) * 10^40
        + 5423026530302404975975171342401962428828) * 10^40
        + 9342487753675956391221805003626300654581) * 10^40
        + 7854271751584149151372321312687668624582) * 10^40
        + 4307161626771620918239035257961352456843) * 10^40
        + 8295646411383673053777076989205548725733) : ℚ) /
        (((((((1754582253346922943181719724296 * 10^40
        + 1352734171408270227310569678102643727375) * 10^40
        + 8038847659365823197405010878197511744985) * 10^40
        + 2496045277645105826259824100056598684661) * 10^40
        + 1121313820067567116670202229910507516198) * 10^40
        + 2009278324467382022144121155251541898865) * 10^40
        + 5617040416021335994300666798549381377615) * 10^40
        + 4838775805363321180247566056021643231232)),
    (((-((((1134 * 10^40
        + 6642304633091809470173203998438863902535) * 10^40
        + 2101181859492993806288600016557553294010) * 10^40
        + 3523459018348985673554038656277733577194) * 10^40
        + 5020424535748707646290079522391903886595)) : ℚ) /
        (((76476189177785328574611042385611299 * 10^40
        + 8473093667377294806372814682806241442816) * 10^40
        + 2471281572568672957538743340740776239243) * 10^40
        + 3566045450675322169103662433992953561088)))

noncomputable def batchC02704PlusMidpointP019Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP019BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP019Center2654‖ ≤ batchC02704PlusMidpointP019Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP019Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP019Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP019Input2654 14 =
      (batchC02704PlusMidpointP019Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP019Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP019Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP019Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP019Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP019Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP019Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP019DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP019Factor2654 * embedPair2542
          batchC02704PlusMidpointP019Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP019Factor2654 : ℝ) *
            batchC02704PlusMidpointP019Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP019Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP019Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP019BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP019Factor2654)

def batchC02704PlusMidpointP020Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((2515138169851860170732905189 : ℚ) /
        236118324143482260684800000000))

def batchC02704PlusMidpointP020Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP020Factor2654 : RatPair2542 := (((((((((((5504 * 10^40
        + 8193007570578346481358262483254968460503) * 10^40
        + 3377460668104466236408275364975115626369) * 10^40
        + 8828975338086349468738790136378376522608) * 10^40
        + 2292387769499138079284427012753117590699) * 10^40
        + 7892426821923227908704912104933942474) * 10^40
        + 8341847589757765287221148528317178814710) * 10^40
        + 1681105620592310276601923766142967388868) * 10^40
        + 9048716782349045567895049051025405698405) : ℚ) /
        (((((((28073316053550767090907515588738 * 10^40
        + 1643746742532323636969114849642299638012) * 10^40
        + 8621562549853171158480174051160187919763) * 10^40
        + 9936724442321693220157185600905578954577) * 10^40
        + 7941021121081073866723235678568120259171) * 10^40
        + 2148453191478112354305938484024670381848) * 10^40
        + 9872646656341375908810668776790102041847) * 10^40
        + 7420412885813138883961056896346291699712)),
    (((-((((14509 * 10^40
        + 4542949320823693182202730201517148328236) * 10^40
        + 6650892047957649502817422077226277576538) * 10^40
        + 2065772255800345950939564089884188759225) * 10^40
        + 8526696245340821105412110117750002771913)) : ℚ) /
        (((917714270133423942895332508627335598 * 10^40
        + 1677124008527537676473776193674897313794) * 10^40
        + 9655378870824075490464920088889314870920) * 10^40
        + 2792545408103866029243949207915442733056)))

noncomputable def batchC02704PlusMidpointP020Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP020BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP020Center2654‖ ≤ batchC02704PlusMidpointP020Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP020Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP020Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP020Input2654 14 =
      (batchC02704PlusMidpointP020Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP020Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP020Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP020Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP020Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP020Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP020Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP020DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP020Factor2654 * embedPair2542
          batchC02704PlusMidpointP020Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP020Factor2654 : ℝ) *
            batchC02704PlusMidpointP020Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP020Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP020Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP020BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP020Factor2654)

def batchC02704PlusMidpointP021Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((2644392173593296965023470597 : ℚ) /
        236118324143482260684800000000))

def batchC02704PlusMidpointP021Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP021Factor2654 : RatPair2542 := (((((((((((5504 * 10^40
        + 8192998140954937911664639257901620730241) * 10^40
        + 1082608351307425814826313788057540738002) * 10^40
        + 3950455158035756665051653693621155181403) * 10^40
        + 4239123051731951975283703427963493375561) * 10^40
        + 8936838506257906233989761255538833198981) * 10^40
        + 5362963817903397477452460326107764628210) * 10^40
        + 8207793354167223469518175223479138433168) * 10^40
        + 6541290844473231828794679786154095204261) : ℚ) /
        (((((((28073316053550767090907515588738 * 10^40
        + 1643746742532323636969114849642299638012) * 10^40
        + 8621562549853171158480174051160187919763) * 10^40
        + 9936724442321693220157185600905578954577) * 10^40
        + 7941021121081073866723235678568120259171) * 10^40
        + 2148453191478112354305938484024670381848) * 10^40
        + 9872646656341375908810668776790102041847) * 10^40
        + 7420412885813138883961056896346291699712)),
    (((-((((5085 * 10^40
        + 337422864705510453876668290915008320411) * 10^40
        + 2686934074749520951546653922122853580741) * 10^40
        + 3612444729989576444234984285572602957932) * 10^40
        + 6597156157427509984029564693373423650083)) : ℚ) /
        (((305904756711141314298444169542445199 * 10^40
        + 3892374669509179225491258731224965771264) * 10^40
        + 9885126290274691830154973362963104956973) * 10^40
        + 4264181802701288676414649735971814244352)))

noncomputable def batchC02704PlusMidpointP021Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP021BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP021Center2654‖ ≤ batchC02704PlusMidpointP021Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP021Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP021Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP021Input2654 14 =
      (batchC02704PlusMidpointP021Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP021Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP021Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP021Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP021Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP021Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP021Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP021DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP021Factor2654 * embedPair2542
          batchC02704PlusMidpointP021Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP021Factor2654 : ℝ) *
            batchC02704PlusMidpointP021Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP021Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP021Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP021BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP021Factor2654)

def batchC02704PlusMidpointP022Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((542109827843102595143241623 : ℚ) /
        47223664828696452136960000000))

def batchC02704PlusMidpointP022Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP022Factor2654 : RatPair2542 := (((((((((((5504 * 10^40
        + 8192993131730781750724908191510128834149) * 10^40
        + 6914838287131878421984676169206096842508) * 10^40
        + 2333972543301139470448622249105819908550) * 10^40
        + 2993890830157306297848982206985633230641) * 10^40
        + 2503292258533432851322077555098146916180) * 10^40
        + 6568761642645668086813032468095624635107) * 10^40
        + 4644700521762322231237424708175137234499) * 10^40
        + 1654642593162762811996552704971046699253) : ℚ) /
        (((((((28073316053550767090907515588738 * 10^40
        + 1643746742532323636969114849642299638012) * 10^40
        + 8621562549853171158480174051160187919763) * 10^40
        + 9936724442321693220157185600905578954577) * 10^40
        + 7941021121081073866723235678568120259171) * 10^40
        + 2148453191478112354305938484024670381848) * 10^40
        + 9872646656341375908810668776790102041847) * 10^40
        + 7420412885813138883961056896346291699712)),
    (((-((((15636 * 10^40
        + 7508238847208931245705906628904111155027) * 10^40
        + 2787667667851305643963112060408178297899) * 10^40
        + 3063559156060328266733906625506080941121) * 10^40
        + 1067213061436704835909523686295141417455)) : ℚ) /
        (((917714270133423942895332508627335598 * 10^40
        + 1677124008527537676473776193674897313794) * 10^40
        + 9655378870824075490464920088889314870920) * 10^40
        + 2792545408103866029243949207915442733056)))

noncomputable def batchC02704PlusMidpointP022Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP022BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP022Center2654‖ ≤ batchC02704PlusMidpointP022Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP022Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP022Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP022Input2654 14 =
      (batchC02704PlusMidpointP022Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP022Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP022Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP022Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP022Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP022Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP022Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP022DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP022Factor2654 * embedPair2542
          batchC02704PlusMidpointP022Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP022Factor2654 : ℝ) *
            batchC02704PlusMidpointP022Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP022Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP022Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP022BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP022Factor2654)

def batchC02704PlusMidpointP023Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((1450645982266156471694092723 : ℚ) /
        118059162071741130342400000000))

def batchC02704PlusMidpointP023Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP023Factor2654 : RatPair2542 := (((((((((((1376 * 10^40
        + 2048244499084028106032937853542134881795) * 10^40
        + 5686628844409270988120883305477038011559) * 10^40
        + 2119501173985509167235116193317697092949) * 10^40
        + 8233395960415383085644274112639420481714) * 10^40
        + 3876224081882319114406608616202064337501) * 10^40
        + 2959793258598179692383271770781629583701) * 10^40
        + 7544277362628498956873057307608659394554) * 10^40
        + 5850676743896181267501673532873203244405) : ℚ) /
        (((((((7018329013387691772726878897184 * 10^40
        + 5410936685633080909242278712410574909503) * 10^40
        + 2155390637463292789620043512790046979940) * 10^40
        + 9984181110580423305039296400226394738644) * 10^40
        + 4485255280270268466680808919642030064792) * 10^40
        + 8037113297869528088576484621006167595462) * 10^40
        + 2468161664085343977202667194197525510461) * 10^40
        + 9355103221453284720990264224086572924928)),
    (((-((((8368 * 10^40
        + 5587655239514257090325454322820892418122) * 10^40
        + 2900754824205140937226706888189458337873) * 10^40
        + 5259020091826573562766662745031343126269) * 10^40
        + 787780854493983708533905354308375382191)) : ℚ) /
        (((458857135066711971447666254313667799 * 10^40
        + 838562004263768838236888096837448656897) * 10^40
        + 4827689435412037745232460044444657435460) * 10^40
        + 1396272704051933014621974603957721366528)))

noncomputable def batchC02704PlusMidpointP023Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP023BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP023Center2654‖ ≤ batchC02704PlusMidpointP023Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP023Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP023Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP023Input2654 14 =
      (batchC02704PlusMidpointP023Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP023Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP023Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP023Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP023Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP023Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP023Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP023DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP023Factor2654 * embedPair2542
          batchC02704PlusMidpointP023Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP023Factor2654 : ℝ) *
            batchC02704PlusMidpointP023Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP023Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP023Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP023BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP023Factor2654)

def batchC02704PlusMidpointP024Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((1494474821378949476104378157 : ℚ) /
        118059162071741130342400000000))

def batchC02704PlusMidpointP024Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP024Factor2654 : RatPair2542 := (((((((((((1376 * 10^40
        + 2048242673914311272966320098940415361302) * 10^40
        + 7693237144824852481854810593211853080312) * 10^40
        + 8780436267052631600075137935189182090340) * 10^40
        + 9844897945949122187573463671921956862677) * 10^40
        + 5138415814629715215801601153338626934394) * 10^40
        + 6389204502921399908135697938739089900964) * 10^40
        + 5818285608736050784796327367768754362610) * 10^40
        + 4784915397098373611493672884652126171445) : ℚ) /
        (((((((7018329013387691772726878897184 * 10^40
        + 5410936685633080909242278712410574909503) * 10^40
        + 2155390637463292789620043512790046979940) * 10^40
        + 9984181110580423305039296400226394738644) * 10^40
        + 4485255280270268466680808919642030064792) * 10^40
        + 8037113297869528088576484621006167595462) * 10^40
        + 2468161664085343977202667194197525510461) * 10^40
        + 9355103221453284720990264224086572924928)),
    (((-((((8621 * 10^40
        + 4007546956467785278177255483695909447275) * 10^40
        + 1705879696246553504378493298137962103609) * 10^40
        + 6769918211128229801989465222756855131403) * 10^40
        + 5259070860209197395616155498131891726769)) : ℚ) /
        (((458857135066711971447666254313667799 * 10^40
        + 838562004263768838236888096837448656897) * 10^40
        + 4827689435412037745232460044444657435460) * 10^40
        + 1396272704051933014621974603957721366528)))

noncomputable def batchC02704PlusMidpointP024Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP024BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP024Center2654‖ ≤ batchC02704PlusMidpointP024Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP024Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP024Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP024Input2654 14 =
      (batchC02704PlusMidpointP024Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP024Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP024Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP024Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP024Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP024Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP024Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP024DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP024Factor2654 * embedPair2542
          batchC02704PlusMidpointP024Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP024Factor2654 : ℝ) *
            batchC02704PlusMidpointP024Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP024Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP024Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP024BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP024Factor2654)

def batchC02704PlusMidpointP025Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((48419629474968996879914223 : ℚ) /
        3689348814741910323200000000))

def batchC02704PlusMidpointP025Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP025Factor2654 : RatPair2542 := (((((((((((1 * 10^40
        + 3439500234676494475731931132867235993217) * 10^40
        + 1269728101708930137804137563819875084984) * 10^40
        + 3838728688588638473711617307140229523761) * 10^40
        + 4860609540197897850713833911532130721346) * 10^40
        + 5010520443956799414536694416087854334384) * 10^40
        + 188375635004875075060086217849466243178) * 10^40
        + 1793751064040223573842487160768606997189) * 10^40
        + 3048900331153416006052089461067706992141) : ℚ) /
        (((((((6853836927136417746803592673 * 10^40
        + 317784117857063555575431912805088452060) * 10^40
        + 617339248669397746864863323742959030253) * 10^40
        + 8486312676865801194633827437890846088611) * 10^40
        + 9574692632109638934049492977460587919985) * 10^40
        + 1492223743454950711024000473262701335542) * 10^40
        + 4436004064125083343727736979681833521006) * 10^40
        + 3104838967989700473360342054906334543872)),
    (((-((((3 * 10^40
        + 2106387261355794386511425795197562170611) * 10^40
        + 8562264572170918974518834600946162570465) * 10^40
        + 8008802223266271312083873055181308685112) * 10^40
        + 7696889080538461176866349879864150060893)) : ℚ) /
        (((164819373227985621928041039624162 * 10^40
        + 2841536839800382100875803479919841037592) * 10^40
        + 2763946727527087657236074877889527534998) * 10^40
        + 3693030270367834746054102720762915848192)))

noncomputable def batchC02704PlusMidpointP025Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP025BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP025Center2654‖ ≤ batchC02704PlusMidpointP025Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP025Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP025Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP025Input2654 14 =
      (batchC02704PlusMidpointP025Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP025Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP025Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP025Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP025Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP025Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP025Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP025DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP025Factor2654 * embedPair2542
          batchC02704PlusMidpointP025Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP025Factor2654 : ℝ) *
            batchC02704PlusMidpointP025Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP025Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP025Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP025BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP025Factor2654)

def batchC02704PlusMidpointP026Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((100349262824676998784528147 : ℚ) /
        7378697629483820646400000000))

def batchC02704PlusMidpointP026Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP026Factor2654 : RatPair2542 := (((((((((((5 * 10^40
        + 3758000928919432835920183427711483348989) * 10^40
        + 654877490703285084885991545617922583152) * 10^40
        + 7294000669902430328121488055453180612899) * 10^40
        + 4955893732350522056264160033974824584895) * 10^40
        + 7190549844793508113312558677134134736255) * 10^40
        + 1627299176759565122390802296832421194507) * 10^40
        + 3524948603052727154080780591558060240446) * 10^40
        + 7188723558522608656634285403527558119605) : ℚ) /
        (((((((27415347708545670987214370692 * 10^40
        + 1271136471428254222301727651220353808240) * 10^40
        + 2469356994677590987459453294971836121015) * 10^40
        + 3945250707463204778535309751563384354447) * 10^40
        + 8298770528438555736197971909842351679940) * 10^40
        + 5968894973819802844096001893050805342169) * 10^40
        + 7744016256500333374910947918727334084025) * 10^40
        + 2419355871958801893441368219625338175488)),
    (((-((((192 * 10^40
        + 9666078173531845951702224881226672669614) * 10^40
        + 6316529627268720189067011495711519246191) * 10^40
        + 6715710896597060884863304303914423879125) * 10^40
        + 7056477730846066781283637302793888614533)) : ℚ) /
        (((9559523647223166071826380298201412 * 10^40
        + 4809136708422161850796601835350780180352) * 10^40
        + 308910196571084119692342917592597029905) * 10^40
        + 4195755681334415271137957804249119195136)))

noncomputable def batchC02704PlusMidpointP026Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP026BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP026Center2654‖ ≤ batchC02704PlusMidpointP026Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP026Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP026Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP026Input2654 14 =
      (batchC02704PlusMidpointP026Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP026Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP026Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP026Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP026Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP026Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP026Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP026DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP026Factor2654 * embedPair2542
          batchC02704PlusMidpointP026Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP026Factor2654 : ℝ) *
            batchC02704PlusMidpointP026Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP026Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP026Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP026BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP026Factor2654)

def batchC02704PlusMidpointP027Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((210828625664342681326447037 : ℚ) /
        14757395258967641292800000000))

def batchC02704PlusMidpointP027Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP027Factor2654 : RatPair2542 := (((((((((((21 * 10^40
        + 5032003656731994586092609652844565291880) * 10^40
        + 1229472950636449887193378191095527825143) * 10^40
        + 6591785286265662649424824900488472918857) * 10^40
        + 7612130177073760620416799224265021206337) * 10^40
        + 6790481829108276790242817108895387109350) * 10^40
        + 9761605263686329142035651615150009967426) * 10^40
        + 3759450975863136570809212343764793074740) * 10^40
        + 675236223837253504389006974816118112341) : ℚ) /
        (((((((109661390834182683948857482768 * 10^40
        + 5084545885713016889206910604881415232960) * 10^40
        + 9877427978710363949837813179887344484061) * 10^40
        + 5781002829852819114141239006253537417791) * 10^40
        + 3195082113754222944791887639369406719762) * 10^40
        + 3875579895279211376384007572203221368679) * 10^40
        + 976065026001333499643791674909336336100) * 10^40
        + 9677423487835207573765472878501352701952)),
    (((-((((1216 * 10^40
        + 2386722158880656798727650976387041287163) * 10^40
        + 8086121137823044789421048667319563597317) * 10^40
        + 392716276082261836624556528802859640961) * 10^40
        + 8464785020087037031968481142013553401729)) : ℚ) /
        (((57357141883338996430958281789208474 * 10^40
        + 8854820250532971104779611012104681082112) * 10^40
        + 1853461179426504718154057505555582179432) * 10^40
        + 5174534088006491626827746825494715170816)))

noncomputable def batchC02704PlusMidpointP027Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP027BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP027Center2654‖ ≤ batchC02704PlusMidpointP027Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP027Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP027Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP027Input2654 14 =
      (batchC02704PlusMidpointP027Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP027Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP027Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP027Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP027Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP027Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP027Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP027DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP027Factor2654 * embedPair2542
          batchC02704PlusMidpointP027Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP027Factor2654 : ℝ) *
            batchC02704PlusMidpointP027Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP027Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP027Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP027BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP027Factor2654)

def batchC02704PlusMidpointP028Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((859357086522682157795940137 : ℚ) /
        59029581035870565171200000000))

def batchC02704PlusMidpointP028Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP028Factor2654 : RatPair2542 := (((((((((((344 * 10^40
        + 512058121482467600580441371454058193275) * 10^40
        + 5073730656548482380945752020104153822405) * 10^40
        + 7521427950889211590496005621386523809229) * 10^40
        + 5939297573264890505855050968481709432095) * 10^40
        + 4095288804648235365691170354182546681728) * 10^40
        + 2387233937612698677087546142536867607444) * 10^40
        + 5005419893665639647200826556430978609538) * 10^40
        + 9251391123785846253351226560630298742461) : ℚ) /
        (((((((1754582253346922943181719724296 * 10^40
        + 1352734171408270227310569678102643727375) * 10^40
        + 8038847659365823197405010878197511744985) * 10^40
        + 2496045277645105826259824100056598684661) * 10^40
        + 1121313820067567116670202229910507516198) * 10^40
        + 2009278324467382022144121155251541898865) * 10^40
        + 5617040416021335994300666798549381377615) * 10^40
        + 4838775805363321180247566056021643231232)),
    (((-((((450 * 10^40
        + 6819950340669733068620127415976584903950) * 10^40
        + 1712411627949866247333392813645588692073) * 10^40
        + 520972373647646959791084659240700564942) * 10^40
        + 1110598163471397169600516341682483274039)) : ℚ) /
        (((20857142503032362338530284286984899 * 10^40
        + 9583571000193807674465313095310793120768) * 10^40
        + 673985883427819897510566365656575337975) * 10^40
        + 4608921486547815137028271572907169153024)))

noncomputable def batchC02704PlusMidpointP028Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP028BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP028Center2654‖ ≤ batchC02704PlusMidpointP028Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP028Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP028Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP028Input2654 14 =
      (batchC02704PlusMidpointP028Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP028Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP028Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP028Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP028Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP028Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP028Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP028DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP028Factor2654 * embedPair2542
          batchC02704PlusMidpointP028Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP028Factor2654 : ℝ) *
            batchC02704PlusMidpointP028Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP028Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP028Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP028BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP028Factor2654)

def batchC02704PlusMidpointP029Input2654 : RatPair2542 := ((((-((771086 * 10^40
        + 2375608422262422295121913714017076035642) * 10^40
        + 892687503977149107256789861968169536293)) : ℚ) /
        ((1564365 * 10^40
        + 640720440591424390853955564729836372211) * 10^40
        + 4037526827959211058494040545689600000000)),
    ((883780890450854350804880629 : ℚ) /
        59029581035870565171200000000))

def batchC02704PlusMidpointP029Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02704PlusMidpointP029Factor2654 : RatPair2542 := (((((((((((344 * 10^40
        + 512057519498059569261976466343738092011) * 10^40
        + 9592941389212229849954041561522240769116) * 10^40
        + 327991200013489572484816592782772641719) * 10^40
        + 1274684125321824581932971245828494019443) * 10^40
        + 5448626483963992092206924440016206079761) * 10^40
        + 3938913655023022126471471013525034955958) * 10^40
        + 945300008052184068420264271493375627818) * 10^40
        + 272452149006651742672458140736493384325) : ℚ) /
        (((((((1754582253346922943181719724296 * 10^40
        + 1352734171408270227310569678102643727375) * 10^40
        + 8038847659365823197405010878197511744985) * 10^40
        + 2496045277645105826259824100056598684661) * 10^40
        + 1121313820067567116670202229910507516198) * 10^40
        + 2009278324467382022144121155251541898865) * 10^40
        + 5617040416021335994300666798549381377615) * 10^40
        + 4838775805363321180247566056021643231232)),
    (((-((((175 * 10^40
        + 8068690158176359726267859552824937749323) * 10^40
        + 4204144601161277837684690860115153229647) * 10^40
        + 4685583891790514088937239946015619317657) * 10^40
        + 3298807145734336917698710657044714307117)) : ℚ) /
        (((7911329914943309852545969901959789 * 10^40
        + 6393768310418340842038567036152369804429) * 10^40
        + 2669442921300207547331594138697321679921) * 10^40
        + 7265452977656067810596930596619960713216)))

noncomputable def batchC02704PlusMidpointP029Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02704PlusMidpointP029BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP029Center2654‖ ≤ batchC02704PlusMidpointP029Error2654
          := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02704PlusMidpointP029Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02704PlusMidpointP029Input2654]
  have hs : compactExp2547 batchC02704PlusMidpointP029Input2654 14 =
      (batchC02704PlusMidpointP029Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02704PlusMidpointP029Input2654 14).2 : ℝ) =
      batchC02704PlusMidpointP029Error2654 :=
      by
    rw [hs]
    norm_num [batchC02704PlusMidpointP029Error2654]
  have h := compactExp_error2547 batchC02704PlusMidpointP029Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      batchC02704PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02704PlusMidpointP029Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02704PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02704PlusMidpointP029Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02704PlusMidpointP029DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP029Factor2654 * embedPair2542
          batchC02704PlusMidpointP029Center2654‖ ≤
        (pairMagnitude2542 batchC02704PlusMidpointP029Factor2654 : ℝ) *
            batchC02704PlusMidpointP029Error2654 := by
  have hx : |batchC02704PlusMidpointPosition2654| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC02704PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchC02704PlusMidpointPosition2654 = embedPair2542
          batchC02704PlusMidpointP029Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02704PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02704PlusMidpointP029Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02704PlusMidpointP029BaseError2654
    (embedPair_magnitude2542 batchC02704PlusMidpointP029Factor2654)

theorem batchC02704PlusMidpointGrid2654 :
    -stripRadius2303 + ((5409 : ℝ) /
        2) * (2 * stripRadius2303 / 10240) =
      batchC02704PlusMidpointPosition2654 := by
  norm_num [stripRadius2303, batchC02704PlusMidpointPosition2654]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP000DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP001DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP002DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP003DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP004DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP005DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP006DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP007DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP008DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP009DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP010DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP011DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP012DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP013DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP014DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP015DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP016DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP017DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP018DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP019DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP020DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP021DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP022DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP023DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP024DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP025DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP026DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP027DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP028DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointP029DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusMidpointGrid2654
