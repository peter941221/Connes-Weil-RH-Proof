import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def kernelN02700MinusPosition2555 : ℝ := (((-7929856121) : ℝ) /
        2560000000)

theorem kernelN02700MinusZero2555 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def kernelN02700MinusP000Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP000Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP000Error2555 : ℝ := 0

theorem kernelN02700MinusP000Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem kernelN02700MinusP000BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP000Center2555‖ ≤ kernelN02700MinusP000Error2555 := by
  rw [kernelN02700MinusP000Exterior2555]
  norm_num [kernelN02700MinusP000Center2555, kernelN02700MinusP000Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP000DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP000Factor2555 * embedPair2542
          kernelN02700MinusP000Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP000Factor2555 : ℝ) * kernelN02700MinusP000Error2555
            := by
  rw [kernelN02700MinusP000Exterior2555]
  norm_num [kernelN02700MinusP000Factor2555, kernelN02700MinusP000Center2555,
      kernelN02700MinusP000Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP001Input2555 : RatPair2542 := ((((-(6688580688215936326964223499725723768788
    *
    10^40
        + 4982692854096728503187522064213490083519)) : ℚ) /
        ((1 * 10^40
        + 8752578370474248106975932892819564741070) * 10^40
        + 9992275832742435204355224137891840000000)),
    ((43806833004475480685705509 : ℚ) /
        184467440737095516160000000))

def kernelN02700MinusP001Center2555 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def kernelN02700MinusP001Factor2555 : RatPair2542 := ((((((((((((((11521 * 10^40
        + 7121473048399654730161167573543111578735) * 10^40
        + 3752496761407523641221792437425822418752) * 10^40
        + 7594972651169930561900138589828042086146) * 10^40
        + 4606100729948807051839586152596482270935) * 10^40
        + 1842616414886654680153298457610686859216) * 10^40
        + 3159460092104327063460641335657517201188) * 10^40
        + 7554333740903967961952501811726269829092) * 10^40
        + 8592362447017109320692807931911064801190) * 10^40
        + 4951765859352178962451887361611755314180) * 10^40
        + 9325299881363737516459353447405022143183) * 10^40
        + 3586071316415337227122515948332324649547) : ℚ) /
        ((((((((((530855096499264200375034182669100673 * 10^40
        + 715392029682525059248925153059675044429) * 10^40
        + 5489363255140266824871665260987928636415) * 10^40
        + 458272112093495727347951208345346508074) * 10^40
        + 9148582145375010260865381697339130077386) * 10^40
        + 7591781714327890688097094366362750108129) * 10^40
        + 6933614735151579388525686059108082363210) * 10^40
        + 6030781413670877109197816563879673208538) * 10^40
        + 6492950348723417282277947976729800937427) * 10^40
        + 2748721362364127200489517533382453361543) * 10^40
        + 8879986962378556953061808521299726696448)),
    (((-((((((((31 * 10^40
        + 6352354484220551287325180315625136572077) * 10^40
        + 6896229487742400908120729495941643238801) * 10^40
        + 7833065965900208729207572964240397562597) * 10^40
        + 7628354762228649222087947020027160631812) * 10^40
        + 3491783133132028094436661824536642692527) * 10^40
        + 5731827727403123955941670785112268570595) * 10^40
        + 3907775764366257312593025594025972884720) * 10^40
        + 5094965062070271481969398698818949316683)) : ℚ) /
        (((((((7299845313529492577405338625902062 * 10^40
        + 5040060464039829882467981137888151089350) * 10^40
        + 7680046837126516249820690069166339688010) * 10^40
        + 4945758958980690475063849034962907971196) * 10^40
        + 5509877864502588213528625647279806208619) * 10^40
        + 8720169451280884093960950506406750384451) * 10^40
        + 8546691820820725614871493256901978037975) * 10^40
        + 4996929156900611117775561124908506284032)))

noncomputable def kernelN02700MinusP001Error2555 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem kernelN02700MinusP001BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP001Center2555‖ ≤ kernelN02700MinusP001Error2555 := by
  have hx : |kernelN02700MinusPosition2555| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [kernelN02700MinusPosition2555, storedWidth]
  have hz : ‖embedPair2542 kernelN02700MinusP001Input2555‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, kernelN02700MinusP001Input2555]
  have hs : compactExp2547 kernelN02700MinusP001Input2555 9 =
      (kernelN02700MinusP001Center2555, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 kernelN02700MinusP001Input2555 9).2 : ℝ) =
      kernelN02700MinusP001Error2555
      := by
    rw [hs]
    norm_num [kernelN02700MinusP001Error2555]
  have h := compactExp_error2547 kernelN02700MinusP001Input2555 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      kernelN02700MinusPosition2555 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          kernelN02700MinusP001Input2555) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [kernelN02700MinusPosition2555, storedWidth,
        nodeModulation2541,
      embedPair2542, kernelN02700MinusP001Input2555, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem kernelN02700MinusP001DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP001Factor2555 * embedPair2542
          kernelN02700MinusP001Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP001Factor2555 : ℝ) * kernelN02700MinusP001Error2555
            := by
  have hx : |kernelN02700MinusPosition2555| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [kernelN02700MinusPosition2555, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) kernelN02700MinusPosition2555 = embedPair2542
          kernelN02700MinusP001Factor2555 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      kernelN02700MinusPosition2555, storedWidth, nodeModulation2541, embedPair2542,
      kernelN02700MinusP001Factor2555, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ kernelN02700MinusP001BaseError2555
    (embedPair_magnitude2542 kernelN02700MinusP001Factor2555)

def kernelN02700MinusP002Input2555 : RatPair2542 := ((((-((17 * 10^40
        + 1805218828286032980113391054520037587918) * 10^40
        + 6926499854364897859155675096110909695679)) : ℚ) /
        ((73 * 10^40
        + 2973526485978139422317359752257065937823) * 10^40
        + 6716006270187613354841793103134720000000)),
    (((-43806833004475480685705509) : ℚ) /
        92233720368547758080000000))

def kernelN02700MinusP002Center2555 : RatPair2542 := ((((-236687586501322481317) : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    (((-10235158114556736630683) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def kernelN02700MinusP002Factor2555 : RatPair2542 := ((((-(((((((((((1562699209463 * 10^40
        + 9483635880084341800320970202033798603835) * 10^40
        + 2688762870594280315996750204970048756235) * 10^40
        + 5026920816541171082537162038962625263019) * 10^40
        + 3171373492602592479216875285296149190524) * 10^40
        + 4503224958929628321986584913607695660472) * 10^40
        + 9946379507824021457130000555040702667805) * 10^40
        + 6896329811707931130316378623366265417924) * 10^40
        + 1126978289455085211610044548066830674119) * 10^40
        + 4563746872408064587857867509368586308816) * 10^40
        + 9043769414630647734094236725815120674118) * 10^40
        + 692283305299619063534042490081458881973)) : ℚ) /
        (((((((((((12114898 * 10^40
        + 808526435114873017777700953161428250352) * 10^40
        + 654977035246259760268619518356430313504) * 10^40
        + 66997916955805644216311755183676721994) * 10^40
        + 6630844278013223882961518184401750937135) * 10^40
        + 6174312101300894008825153507630529833013) * 10^40
        + 2241880182730136398551076257160017283966) * 10^40
        + 1784056612655200506715307522328759125821) * 10^40
        + 6511239150957279482391535525021371145080) * 10^40
        + 8926853851767160798356756790048568749286) * 10^40
        + 6309802908408506998128790377591588177656) * 10^40
        + 5298436988590367697105894115527274528768)),
    ((((((((((3601696 * 10^40
        + 7767243540955205344098121102824310555724) * 10^40
        + 6355037638947329445534766676274298534346) * 10^40
        + 8435986970516975319038886125329488122665) * 10^40
        + 9448147559393356730801016548178914208019) * 10^40
        + 9831316576706249419094676312402844732638) * 10^40
        + 6163382750166171404378336560424080323887) * 10^40
        + 4326001758627666014664467595219230194609) * 10^40
        + 3490676614232213676709022292528384933963) : ℚ) /
        ((((((((27 * 10^40
        + 2610663525562379419552896007600270606803) * 10^40
        + 6063064689458095386466352056150455113401) * 10^40
        + 119106213456037419595487161540470251152) * 10^40
        + 5026560681324236180341400296724160954667) * 10^40
        + 4615026096081574931661867517444799672804) * 10^40
        + 8762536589996236920173911548894242629877) * 10^40
        + 8765772211137353631322503631410017498) * 10^40
        + 3069405594712846138679290003867830321152)))

noncomputable def kernelN02700MinusP002Error2555 : ℝ := ((23242280564835055193 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem kernelN02700MinusP002BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP002Center2555‖ ≤ kernelN02700MinusP002Error2555 := by
  have hx : |kernelN02700MinusPosition2555| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [kernelN02700MinusPosition2555, storedWidth]
  have hz : ‖embedPair2542 kernelN02700MinusP002Input2555‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, kernelN02700MinusP002Input2555]
  have hs : compactExp2547 kernelN02700MinusP002Input2555 8 =
      (kernelN02700MinusP002Center2555, ((23242280564835055193 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 kernelN02700MinusP002Input2555 8).2 : ℝ) =
      kernelN02700MinusP002Error2555
      := by
    rw [hs]
    norm_num [kernelN02700MinusP002Error2555]
  have h := compactExp_error2547 kernelN02700MinusP002Input2555 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      kernelN02700MinusPosition2555 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          kernelN02700MinusP002Input2555) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [kernelN02700MinusPosition2555, storedWidth,
        nodeModulation2541,
      embedPair2542, kernelN02700MinusP002Input2555, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem kernelN02700MinusP002DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP002Factor2555 * embedPair2542
          kernelN02700MinusP002Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP002Factor2555 : ℝ) * kernelN02700MinusP002Error2555
            := by
  have hx : |kernelN02700MinusPosition2555| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [kernelN02700MinusPosition2555, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) kernelN02700MinusPosition2555 = embedPair2542
          kernelN02700MinusP002Factor2555 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      kernelN02700MinusPosition2555, storedWidth, nodeModulation2541, embedPair2542,
      kernelN02700MinusP002Factor2555, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ kernelN02700MinusP002BaseError2555
    (embedPair_magnitude2542 kernelN02700MinusP002Factor2555)

def kernelN02700MinusP003Input2555 : RatPair2542 := ((((-((2247 * 10^40
        + 2994581517147963196032705765199078519641) * 10^40
        + 1994410414746225504961591598744160567733)) : ℚ) /
        ((13284 * 10^40
        + 922703065279921881810676711054660831348) * 10^40
        + 9952512674799299317166344800829440000000)),
    (((-43806833004475480685705509) : ℚ) /
        92233720368547758080000000))

def kernelN02700MinusP003Center2555 : RatPair2542 := ((((-67562655288918125376430023877) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-45650528571176392534168394947) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def kernelN02700MinusP003Factor2555 : RatPair2542 := ((((-(((((((((((717393984927880351039617248 *
    10^40
        + 9262082268064721215811622221302376212407) * 10^40
        + 1594993494155409791634470764335783092579) * 10^40
        + 2165432693994442763605086589261878923443) * 10^40
        + 7682296494980480592995303994766203674437) * 10^40
        + 7798035342899555285732667121059437949682) * 10^40
        + 1617216634899505125718925347329911940978) * 10^40
        + 946664143809013718124666746074203865414) * 10^40
        + 3662149094957686264421297912674597789252) * 10^40
        + 1444945339694797498131364899600137799859) * 10^40
        + 8788471159846505326015818240176789576878) * 10^40
        + 7745062014984922621517930541150251244719)) : ℚ) /
        (((((((((((11591645624957923641255 * 10^40
        + 7169307872138455404407220793325865774016) * 10^40
        + 1306576402704904108300689441178374989106) * 10^40
        + 3337009721098198857409058631031722259601) * 10^40
        + 9840504720346373095684392942248556673910) * 10^40
        + 188874464745142484446815513898313297959) * 10^40
        + 3895234986689035515941419368241724842493) * 10^40
        + 7572594310394036144173205388518287780874) * 10^40
        + 4382400772073097468240060841430635623810) * 10^40
        + 8394407883881474032463357826835105430657) * 10^40
        + 471503876859420940021589950296099627515) * 10^40
        + 2477037911601278867886710049441373487104)),
    (((-((((((((1162873131168331 * 10^40
        + 822749623944339559264983732505361861284) * 10^40
        + 8110090003937128111254467060289669626962) * 10^40
        + 2853251875214068360792621095807793878359) * 10^40
        + 3300407081189537985413700846357661646535) * 10^40
        + 4524333828406294211467472649888556708707) * 10^40
        + 3403570001547427834075463161187166502902) * 10^40
        + 7465322255848927481501450763723499898958) * 10^40
        + 196093552903057104148574790217223191717)) : ℚ) /
        ((((((((29411502928 * 10^40
        + 107965064720505489447392351946316508944) * 10^40
        + 570954626614098327124123755152464922891) * 10^40
        + 2877605674389988743713106167413174053831) * 10^40
        + 7239508824147568550728793920929118234919) * 10^40
        + 8857157502476592489823314064997997943306) * 10^40
        + 1804629076702604115588829234849554350924) * 10^40
        + 4283956541675445184864963615547766928589) * 10^40
        + 9582731533623441209194749549825000210432)))

noncomputable def kernelN02700MinusP003Error2555 : ℝ := ((48559493963991329543302431 : ℝ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))

theorem kernelN02700MinusP003BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP003Center2555‖ ≤ kernelN02700MinusP003Error2555 := by
  have hx : |kernelN02700MinusPosition2555| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [kernelN02700MinusPosition2555, storedWidth]
  have hz : ‖embedPair2542 kernelN02700MinusP003Input2555‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, kernelN02700MinusP003Input2555]
  have hs : compactExp2547 kernelN02700MinusP003Input2555 8 =
      (kernelN02700MinusP003Center2555, ((48559493963991329543302431 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 kernelN02700MinusP003Input2555 8).2 : ℝ) =
      kernelN02700MinusP003Error2555
      := by
    rw [hs]
    norm_num [kernelN02700MinusP003Error2555]
  have h := compactExp_error2547 kernelN02700MinusP003Input2555 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      kernelN02700MinusPosition2555 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          kernelN02700MinusP003Input2555) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [kernelN02700MinusPosition2555, storedWidth,
        nodeModulation2541,
      embedPair2542, kernelN02700MinusP003Input2555, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem kernelN02700MinusP003DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP003Factor2555 * embedPair2542
          kernelN02700MinusP003Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP003Factor2555 : ℝ) * kernelN02700MinusP003Error2555
            := by
  have hx : |kernelN02700MinusPosition2555| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [kernelN02700MinusPosition2555, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) kernelN02700MinusPosition2555 = embedPair2542
          kernelN02700MinusP003Factor2555 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      kernelN02700MinusPosition2555, storedWidth, nodeModulation2541, embedPair2542,
      kernelN02700MinusP003Factor2555, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ kernelN02700MinusP003BaseError2555
    (embedPair_magnitude2542 kernelN02700MinusP003Factor2555)

def kernelN02700MinusP004Input2555 : RatPair2542 := ((((-((38 * 10^40
        + 8185595921673939082042460559705933328710) * 10^40
        + 152439585550817995883152104899972195679)) : ℚ) /
        ((267 * 10^40
        + 9934518708431604868451190036789843840469) * 10^40
        + 7242920599205959594841793103134720000000)),
    ((43806833004475480685705509 : ℚ) /
        92233720368547758080000000))

def kernelN02700MinusP004Center2555 : RatPair2542 := ((((-68389271845661481738864442245855) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((92418108643056889386327940952689 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def kernelN02700MinusP004Factor2555 : RatPair2542 := ((((-(((((((((((887150240016204 * 10^40
        + 3162786135989544168756856030840277349897) * 10^40
        + 7857129421777376559125287403485252477229) * 10^40
        + 29237833804928050464698465675966961490) * 10^40
        + 5586907399380343414568585227338610783538) * 10^40
        + 775837930836816088022117465176622830043) * 10^40
        + 4655480008295771197471232803852307148168) * 10^40
        + 9162575583401279509078525303191514875212) * 10^40
        + 6231480946690114137396508091425235916023) * 10^40
        + 2812667354603142366565793177596612663203) * 10^40
        + 6546818755742994403953772620567999616863) * 10^40
        + 2807893286229258779475082288909583881973)) : ℚ) /
        (((((((((((28942438972 * 10^40
        + 3657646772279795725887540344474329274315) * 10^40
        + 3959325550306428794551586301701551816782) * 10^40
        + 6192740838979085908754914458596252577942) * 10^40
        + 1132446609039100958234748718225104215413) * 10^40
        + 9051242576597935768780229020676597808408) * 10^40
        + 6802209594057265208799415035889783174068) * 10^40
        + 5260834448098122429992084481393987137970) * 10^40
        + 1532484656859527888074553476657700266655) * 10^40
        + 6150862715353027237022237965886408319713) * 10^40
        + 9169981849055012881150024208049122294911) * 10^40
        + 8611116161343013813318630115527274528768)),
    ((((((((((271933005 * 10^40
        + 5725257773977397853806079724647556064352) * 10^40
        + 1036215745923009921035983665616443023535) * 10^40
        + 7571172381565667757084855011229266284075) * 10^40
        + 2158444002387872940766239123313234430493) * 10^40
        + 7206586460270467119727938034791567965263) * 10^40
        + 6613693946363914220930352733667826580559) * 10^40
        + 4576889735237925717401184169236026954783) * 10^40
        + 1714243707384774971911744781690365066037) : ℚ) /
        ((((((((4871 * 10^40
        + 7659315104606025147200408996023734269028) * 10^40
        + 8224330893135061231407877888946841612744) * 10^40
        + 4156179482148062401670989876663191453274) * 10^40
        + 9361997009934290183253537725993980116759) * 10^40
        + 1697904539460718883964967176616423492020) * 10^40
        + 6924729299185745215261580734292228090225) * 10^40
        + 423453899942074101460331283842958437764) * 10^40
        + 275001873072231092396026003867830321152)))

noncomputable def kernelN02700MinusP004Error2555 : ℝ := ((383779637246708834189989500561 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem kernelN02700MinusP004BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP004Center2555‖ ≤ kernelN02700MinusP004Error2555 := by
  have hx : |kernelN02700MinusPosition2555| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [kernelN02700MinusPosition2555, storedWidth]
  have hz : ‖embedPair2542 kernelN02700MinusP004Input2555‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, kernelN02700MinusP004Input2555]
  have hs : compactExp2547 kernelN02700MinusP004Input2555 8 =
      (kernelN02700MinusP004Center2555, ((383779637246708834189989500561 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 kernelN02700MinusP004Input2555 8).2 : ℝ) =
      kernelN02700MinusP004Error2555
      := by
    rw [hs]
    norm_num [kernelN02700MinusP004Error2555]
  have h := compactExp_error2547 kernelN02700MinusP004Input2555 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      kernelN02700MinusPosition2555 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          kernelN02700MinusP004Input2555) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [kernelN02700MinusPosition2555, storedWidth,
        nodeModulation2541,
      embedPair2542, kernelN02700MinusP004Input2555, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem kernelN02700MinusP004DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP004Factor2555 * embedPair2542
          kernelN02700MinusP004Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP004Factor2555 : ℝ) * kernelN02700MinusP004Error2555
            := by
  have hx : |kernelN02700MinusPosition2555| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [kernelN02700MinusPosition2555, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) kernelN02700MinusPosition2555 = embedPair2542
          kernelN02700MinusP004Factor2555 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      kernelN02700MinusPosition2555, storedWidth, nodeModulation2541, embedPair2542,
      kernelN02700MinusP004Factor2555, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ kernelN02700MinusP004BaseError2555
    (embedPair_magnitude2542 kernelN02700MinusP004Factor2555)

def kernelN02700MinusP005Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP005Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP005Error2555 : ℝ := 0

theorem kernelN02700MinusP005Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem kernelN02700MinusP005BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP005Center2555‖ ≤ kernelN02700MinusP005Error2555 := by
  rw [kernelN02700MinusP005Exterior2555]
  norm_num [kernelN02700MinusP005Center2555, kernelN02700MinusP005Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP005DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP005Factor2555 * embedPair2542
          kernelN02700MinusP005Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP005Factor2555 : ℝ) * kernelN02700MinusP005Error2555
            := by
  rw [kernelN02700MinusP005Exterior2555]
  norm_num [kernelN02700MinusP005Factor2555, kernelN02700MinusP005Center2555,
      kernelN02700MinusP005Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP006Input2555 : RatPair2542 := ((((-5257757264283175625308744953187) : ℚ) /
        9169574712713507276718080000000),
    ((0 : ℚ) /
        1))

def kernelN02700MinusP006Center2555 : RatPair2542 := (((19504508082407141 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def kernelN02700MinusP006Factor2555 : RatPair2542 := ((((((548 * 10^40
        + 2217242802806526105122040167882402958868) * 10^40
        + 3577031725696915406875449055140609366944) * 10^40
        + 6322237363435073701204128791556243999117) : ℚ) /
        ((16205757207505281662197928304602393680 * 10^40
        + 5293276773758322903228484500985510207016) * 10^40
        + 9958614357229206230366969667550048007064)),
    ((0 : ℚ) /
        1))

noncomputable def kernelN02700MinusP006Error2555 : ℝ := ((7069434267121 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem kernelN02700MinusP006BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP006Center2555‖ ≤ kernelN02700MinusP006Error2555 := by
  have hx : |kernelN02700MinusPosition2555| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [kernelN02700MinusPosition2555, storedWidth]
  have hz : ‖embedPair2542 kernelN02700MinusP006Input2555‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, kernelN02700MinusP006Input2555]
  have hs : compactExp2547 kernelN02700MinusP006Input2555 7 =
      (kernelN02700MinusP006Center2555, ((7069434267121 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 kernelN02700MinusP006Input2555 7).2 : ℝ) =
      kernelN02700MinusP006Error2555
      := by
    rw [hs]
    norm_num [kernelN02700MinusP006Error2555]
  have h := compactExp_error2547 kernelN02700MinusP006Input2555 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      kernelN02700MinusPosition2555 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          kernelN02700MinusP006Input2555) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [kernelN02700MinusPosition2555, storedWidth,
        nodeModulation2541,
      embedPair2542, kernelN02700MinusP006Input2555, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem kernelN02700MinusP006DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP006Factor2555 * embedPair2542
          kernelN02700MinusP006Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP006Factor2555 : ℝ) * kernelN02700MinusP006Error2555
            := by
  have hx : |kernelN02700MinusPosition2555| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [kernelN02700MinusPosition2555, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) kernelN02700MinusPosition2555 = embedPair2542
          kernelN02700MinusP006Factor2555 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      kernelN02700MinusPosition2555, storedWidth, nodeModulation2541, embedPair2542,
      kernelN02700MinusP006Factor2555, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ kernelN02700MinusP006BaseError2555
    (embedPair_magnitude2542 kernelN02700MinusP006Factor2555)

def kernelN02700MinusP007Input2555 : RatPair2542 := ((((-((2247 * 10^40
        + 2994581517147963196032705765199078519641) * 10^40
        + 1994410414746225504961591598744160567733)) : ℚ) /
        ((3321 * 10^40
        + 230675766319980470452669177763665207837) * 10^40
        + 2488128168699824829291586200207360000000)),
    ((0 : ℚ) /
        1))

def kernelN02700MinusP007Center2555 : RatPair2542 := (((227161576196330745979291438463 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def kernelN02700MinusP007Factor2555 : RatPair2542 :=
    (((((((((((((49093456061205968292650857126226688234 *
    10^40
        + 6387412514107188100951604305244160599244) * 10^40
        + 9047068664327313450350968284577184897364) * 10^40
        + 5669123449380954279200175924008288647148) * 10^40
        + 6923170734133161370787517498381629646320) * 10^40
        + 778440067353998280749436958330890880684) * 10^40
        + 646535933488048106591229142139313368884) * 10^40
        + 3518669294996016846578046225371571400049) * 10^40
        + 6072664609360804977238541340257937431574) * 10^40
        + 8405960618696692838647044546521562513241) * 10^40
        + 4206683842178217320550522511452580728797) : ℚ) /
        ((((((((((23409141915406051220036596658895703 * 10^40
        + 5270335118167222874082409338211804987319) * 10^40
        + 5727870704272825401770771079948171924854) * 10^40
        + 4571321504451550502214877018424552369447) * 10^40
        + 6206290265870300972842205837835135493640) * 10^40
        + 2551309011635991958953513571342238531357) * 10^40
        + 1512628219746634169991264988968568996042) * 10^40
        + 2805410045528479718635674533668031308830) * 10^40
        + 8069202893520658185802766719817315057560) * 10^40
        + 4425240148047063462268328888531805988781) * 10^40
        + 6331405806574261435595819908379354169624)),
    ((0 : ℚ) /
        1))

noncomputable def kernelN02700MinusP007Error2555 : ℝ := ((31448282402248334335030421 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem kernelN02700MinusP007BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP007Center2555‖ ≤ kernelN02700MinusP007Error2555 := by
  have hx : |kernelN02700MinusPosition2555| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [kernelN02700MinusPosition2555, storedWidth]
  have hz : ‖embedPair2542 kernelN02700MinusP007Input2555‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, kernelN02700MinusP007Input2555]
  have hs : compactExp2547 kernelN02700MinusP007Input2555 6 =
      (kernelN02700MinusP007Center2555, ((31448282402248334335030421 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 kernelN02700MinusP007Input2555 6).2 : ℝ) =
      kernelN02700MinusP007Error2555
      := by
    rw [hs]
    norm_num [kernelN02700MinusP007Error2555]
  have h := compactExp_error2547 kernelN02700MinusP007Input2555 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      kernelN02700MinusPosition2555 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          kernelN02700MinusP007Input2555) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [kernelN02700MinusPosition2555, storedWidth,
        nodeModulation2541,
      embedPair2542, kernelN02700MinusP007Input2555, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem kernelN02700MinusP007DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP007Factor2555 * embedPair2542
          kernelN02700MinusP007Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP007Factor2555 : ℝ) * kernelN02700MinusP007Error2555
            := by
  have hx : |kernelN02700MinusPosition2555| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [kernelN02700MinusPosition2555, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) kernelN02700MinusPosition2555 = embedPair2542
          kernelN02700MinusP007Factor2555 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      kernelN02700MinusPosition2555, storedWidth, nodeModulation2541, embedPair2542,
      kernelN02700MinusP007Factor2555, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ kernelN02700MinusP007BaseError2555
    (embedPair_magnitude2542 kernelN02700MinusP007Factor2555)

def kernelN02700MinusP008Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP008Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP008Error2555 : ℝ := 0

theorem kernelN02700MinusP008Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨8, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
    (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx

theorem kernelN02700MinusP008BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP008Center2555‖ ≤ kernelN02700MinusP008Error2555 := by
  rw [kernelN02700MinusP008Exterior2555]
  norm_num [kernelN02700MinusP008Center2555, kernelN02700MinusP008Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP008DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP008Factor2555 * embedPair2542
          kernelN02700MinusP008Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP008Factor2555 : ℝ) * kernelN02700MinusP008Error2555
            := by
  rw [kernelN02700MinusP008Exterior2555]
  norm_num [kernelN02700MinusP008Factor2555, kernelN02700MinusP008Center2555,
      kernelN02700MinusP008Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP009Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP009Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP009Error2555 : ℝ := 0

theorem kernelN02700MinusP009Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨9, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
    (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx

theorem kernelN02700MinusP009BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP009Center2555‖ ≤ kernelN02700MinusP009Error2555 := by
  rw [kernelN02700MinusP009Exterior2555]
  norm_num [kernelN02700MinusP009Center2555, kernelN02700MinusP009Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP009DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ kernelN02700MinusPosition2555 -
      embedPair2542 kernelN02700MinusP009Factor2555 * embedPair2542
          kernelN02700MinusP009Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP009Factor2555 : ℝ) * kernelN02700MinusP009Error2555
            := by
  rw [kernelN02700MinusP009Exterior2555]
  norm_num [kernelN02700MinusP009Factor2555, kernelN02700MinusP009Center2555,
      kernelN02700MinusP009Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP010Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP010Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP010Error2555 : ℝ := 0

theorem kernelN02700MinusP010Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨10, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
    (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx

theorem kernelN02700MinusP010BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP010Center2555‖ ≤ kernelN02700MinusP010Error2555 := by
  rw [kernelN02700MinusP010Exterior2555]
  norm_num [kernelN02700MinusP010Center2555, kernelN02700MinusP010Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP010DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP010Factor2555 * embedPair2542
          kernelN02700MinusP010Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP010Factor2555 : ℝ) * kernelN02700MinusP010Error2555
            := by
  rw [kernelN02700MinusP010Exterior2555]
  norm_num [kernelN02700MinusP010Factor2555, kernelN02700MinusP010Center2555,
      kernelN02700MinusP010Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP011Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP011Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP011Error2555 : ℝ := 0

theorem kernelN02700MinusP011Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨11, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
    (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx

theorem kernelN02700MinusP011BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP011Center2555‖ ≤ kernelN02700MinusP011Error2555 := by
  rw [kernelN02700MinusP011Exterior2555]
  norm_num [kernelN02700MinusP011Center2555, kernelN02700MinusP011Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP011DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP011Factor2555 * embedPair2542
          kernelN02700MinusP011Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP011Factor2555 : ℝ) * kernelN02700MinusP011Error2555
            := by
  rw [kernelN02700MinusP011Exterior2555]
  norm_num [kernelN02700MinusP011Factor2555, kernelN02700MinusP011Center2555,
      kernelN02700MinusP011Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP012Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP012Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP012Error2555 : ℝ := 0

theorem kernelN02700MinusP012Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨12, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
    (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx

theorem kernelN02700MinusP012BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP012Center2555‖ ≤ kernelN02700MinusP012Error2555 := by
  rw [kernelN02700MinusP012Exterior2555]
  norm_num [kernelN02700MinusP012Center2555, kernelN02700MinusP012Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP012DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP012Factor2555 * embedPair2542
          kernelN02700MinusP012Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP012Factor2555 : ℝ) * kernelN02700MinusP012Error2555
            := by
  rw [kernelN02700MinusP012Exterior2555]
  norm_num [kernelN02700MinusP012Factor2555, kernelN02700MinusP012Center2555,
      kernelN02700MinusP012Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP013Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP013Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP013Error2555 : ℝ := 0

theorem kernelN02700MinusP013Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨13, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
    (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx

theorem kernelN02700MinusP013BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP013Center2555‖ ≤ kernelN02700MinusP013Error2555 := by
  rw [kernelN02700MinusP013Exterior2555]
  norm_num [kernelN02700MinusP013Center2555, kernelN02700MinusP013Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP013DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP013Factor2555 * embedPair2542
          kernelN02700MinusP013Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP013Factor2555 : ℝ) * kernelN02700MinusP013Error2555
            := by
  rw [kernelN02700MinusP013Exterior2555]
  norm_num [kernelN02700MinusP013Factor2555, kernelN02700MinusP013Center2555,
      kernelN02700MinusP013Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP014Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP014Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP014Error2555 : ℝ := 0

theorem kernelN02700MinusP014Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨14, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
    (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx

theorem kernelN02700MinusP014BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP014Center2555‖ ≤ kernelN02700MinusP014Error2555 := by
  rw [kernelN02700MinusP014Exterior2555]
  norm_num [kernelN02700MinusP014Center2555, kernelN02700MinusP014Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP014DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP014Factor2555 * embedPair2542
          kernelN02700MinusP014Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP014Factor2555 : ℝ) * kernelN02700MinusP014Error2555
            := by
  rw [kernelN02700MinusP014Exterior2555]
  norm_num [kernelN02700MinusP014Factor2555, kernelN02700MinusP014Center2555,
      kernelN02700MinusP014Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP015Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP015Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP015Error2555 : ℝ := 0

theorem kernelN02700MinusP015Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨15, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
    (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx

theorem kernelN02700MinusP015BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP015Center2555‖ ≤ kernelN02700MinusP015Error2555 := by
  rw [kernelN02700MinusP015Exterior2555]
  norm_num [kernelN02700MinusP015Center2555, kernelN02700MinusP015Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP015DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP015Factor2555 * embedPair2542
          kernelN02700MinusP015Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP015Factor2555 : ℝ) * kernelN02700MinusP015Error2555
            := by
  rw [kernelN02700MinusP015Exterior2555]
  norm_num [kernelN02700MinusP015Factor2555, kernelN02700MinusP015Center2555,
      kernelN02700MinusP015Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP016Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP016Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP016Error2555 : ℝ := 0

theorem kernelN02700MinusP016Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨16, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
    (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx

theorem kernelN02700MinusP016BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP016Center2555‖ ≤ kernelN02700MinusP016Error2555 := by
  rw [kernelN02700MinusP016Exterior2555]
  norm_num [kernelN02700MinusP016Center2555, kernelN02700MinusP016Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP016DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP016Factor2555 * embedPair2542
          kernelN02700MinusP016Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP016Factor2555 : ℝ) * kernelN02700MinusP016Error2555
            := by
  rw [kernelN02700MinusP016Exterior2555]
  norm_num [kernelN02700MinusP016Factor2555, kernelN02700MinusP016Center2555,
      kernelN02700MinusP016Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP017Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP017Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP017Error2555 : ℝ := 0

theorem kernelN02700MinusP017Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨17, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
    (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx

theorem kernelN02700MinusP017BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP017Center2555‖ ≤ kernelN02700MinusP017Error2555 := by
  rw [kernelN02700MinusP017Exterior2555]
  norm_num [kernelN02700MinusP017Center2555, kernelN02700MinusP017Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP017DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP017Factor2555 * embedPair2542
          kernelN02700MinusP017Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP017Factor2555 : ℝ) * kernelN02700MinusP017Error2555
            := by
  rw [kernelN02700MinusP017Exterior2555]
  norm_num [kernelN02700MinusP017Factor2555, kernelN02700MinusP017Center2555,
      kernelN02700MinusP017Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP018Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP018Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP018Error2555 : ℝ := 0

theorem kernelN02700MinusP018Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨18, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
    (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx

theorem kernelN02700MinusP018BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP018Center2555‖ ≤ kernelN02700MinusP018Error2555 := by
  rw [kernelN02700MinusP018Exterior2555]
  norm_num [kernelN02700MinusP018Center2555, kernelN02700MinusP018Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP018DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP018Factor2555 * embedPair2542
          kernelN02700MinusP018Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP018Factor2555 : ℝ) * kernelN02700MinusP018Error2555
            := by
  rw [kernelN02700MinusP018Exterior2555]
  norm_num [kernelN02700MinusP018Factor2555, kernelN02700MinusP018Center2555,
      kernelN02700MinusP018Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP019Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP019Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP019Error2555 : ℝ := 0

theorem kernelN02700MinusP019Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨19, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
    (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx

theorem kernelN02700MinusP019BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP019Center2555‖ ≤ kernelN02700MinusP019Error2555 := by
  rw [kernelN02700MinusP019Exterior2555]
  norm_num [kernelN02700MinusP019Center2555, kernelN02700MinusP019Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP019DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP019Factor2555 * embedPair2542
          kernelN02700MinusP019Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP019Factor2555 : ℝ) * kernelN02700MinusP019Error2555
            := by
  rw [kernelN02700MinusP019Exterior2555]
  norm_num [kernelN02700MinusP019Factor2555, kernelN02700MinusP019Center2555,
      kernelN02700MinusP019Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP020Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP020Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP020Error2555 : ℝ := 0

theorem kernelN02700MinusP020Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨20, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
    (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx

theorem kernelN02700MinusP020BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP020Center2555‖ ≤ kernelN02700MinusP020Error2555 := by
  rw [kernelN02700MinusP020Exterior2555]
  norm_num [kernelN02700MinusP020Center2555, kernelN02700MinusP020Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP020DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP020Factor2555 * embedPair2542
          kernelN02700MinusP020Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP020Factor2555 : ℝ) * kernelN02700MinusP020Error2555
            := by
  rw [kernelN02700MinusP020Exterior2555]
  norm_num [kernelN02700MinusP020Factor2555, kernelN02700MinusP020Center2555,
      kernelN02700MinusP020Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP021Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP021Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP021Error2555 : ℝ := 0

theorem kernelN02700MinusP021Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨21, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
    (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx

theorem kernelN02700MinusP021BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP021Center2555‖ ≤ kernelN02700MinusP021Error2555 := by
  rw [kernelN02700MinusP021Exterior2555]
  norm_num [kernelN02700MinusP021Center2555, kernelN02700MinusP021Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP021DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP021Factor2555 * embedPair2542
          kernelN02700MinusP021Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP021Factor2555 : ℝ) * kernelN02700MinusP021Error2555
            := by
  rw [kernelN02700MinusP021Exterior2555]
  norm_num [kernelN02700MinusP021Factor2555, kernelN02700MinusP021Center2555,
      kernelN02700MinusP021Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP022Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP022Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP022Error2555 : ℝ := 0

theorem kernelN02700MinusP022Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨22, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
    (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx

theorem kernelN02700MinusP022BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP022Center2555‖ ≤ kernelN02700MinusP022Error2555 := by
  rw [kernelN02700MinusP022Exterior2555]
  norm_num [kernelN02700MinusP022Center2555, kernelN02700MinusP022Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP022DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP022Factor2555 * embedPair2542
          kernelN02700MinusP022Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP022Factor2555 : ℝ) * kernelN02700MinusP022Error2555
            := by
  rw [kernelN02700MinusP022Exterior2555]
  norm_num [kernelN02700MinusP022Factor2555, kernelN02700MinusP022Center2555,
      kernelN02700MinusP022Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP023Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP023Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP023Error2555 : ℝ := 0

theorem kernelN02700MinusP023Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨23, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
    (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx

theorem kernelN02700MinusP023BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP023Center2555‖ ≤ kernelN02700MinusP023Error2555 := by
  rw [kernelN02700MinusP023Exterior2555]
  norm_num [kernelN02700MinusP023Center2555, kernelN02700MinusP023Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP023DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP023Factor2555 * embedPair2542
          kernelN02700MinusP023Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP023Factor2555 : ℝ) * kernelN02700MinusP023Error2555
            := by
  rw [kernelN02700MinusP023Exterior2555]
  norm_num [kernelN02700MinusP023Factor2555, kernelN02700MinusP023Center2555,
      kernelN02700MinusP023Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP024Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP024Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP024Error2555 : ℝ := 0

theorem kernelN02700MinusP024Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨24, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
    (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx

theorem kernelN02700MinusP024BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP024Center2555‖ ≤ kernelN02700MinusP024Error2555 := by
  rw [kernelN02700MinusP024Exterior2555]
  norm_num [kernelN02700MinusP024Center2555, kernelN02700MinusP024Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP024DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP024Factor2555 * embedPair2542
          kernelN02700MinusP024Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP024Factor2555 : ℝ) * kernelN02700MinusP024Error2555
            := by
  rw [kernelN02700MinusP024Exterior2555]
  norm_num [kernelN02700MinusP024Factor2555, kernelN02700MinusP024Center2555,
      kernelN02700MinusP024Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP025Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP025Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP025Error2555 : ℝ := 0

theorem kernelN02700MinusP025Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨25, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
    (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx

theorem kernelN02700MinusP025BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP025Center2555‖ ≤ kernelN02700MinusP025Error2555 := by
  rw [kernelN02700MinusP025Exterior2555]
  norm_num [kernelN02700MinusP025Center2555, kernelN02700MinusP025Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP025DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP025Factor2555 * embedPair2542
          kernelN02700MinusP025Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP025Factor2555 : ℝ) * kernelN02700MinusP025Error2555
            := by
  rw [kernelN02700MinusP025Exterior2555]
  norm_num [kernelN02700MinusP025Factor2555, kernelN02700MinusP025Center2555,
      kernelN02700MinusP025Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP026Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP026Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP026Error2555 : ℝ := 0

theorem kernelN02700MinusP026Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨26, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
    (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx

theorem kernelN02700MinusP026BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP026Center2555‖ ≤ kernelN02700MinusP026Error2555 := by
  rw [kernelN02700MinusP026Exterior2555]
  norm_num [kernelN02700MinusP026Center2555, kernelN02700MinusP026Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP026DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP026Factor2555 * embedPair2542
          kernelN02700MinusP026Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP026Factor2555 : ℝ) * kernelN02700MinusP026Error2555
            := by
  rw [kernelN02700MinusP026Exterior2555]
  norm_num [kernelN02700MinusP026Factor2555, kernelN02700MinusP026Center2555,
      kernelN02700MinusP026Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP027Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP027Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP027Error2555 : ℝ := 0

theorem kernelN02700MinusP027Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨27, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
    (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx

theorem kernelN02700MinusP027BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP027Center2555‖ ≤ kernelN02700MinusP027Error2555 := by
  rw [kernelN02700MinusP027Exterior2555]
  norm_num [kernelN02700MinusP027Center2555, kernelN02700MinusP027Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP027DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP027Factor2555 * embedPair2542
          kernelN02700MinusP027Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP027Factor2555 : ℝ) * kernelN02700MinusP027Error2555
            := by
  rw [kernelN02700MinusP027Exterior2555]
  norm_num [kernelN02700MinusP027Factor2555, kernelN02700MinusP027Center2555,
      kernelN02700MinusP027Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP028Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP028Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP028Error2555 : ℝ := 0

theorem kernelN02700MinusP028Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨28, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
    (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx

theorem kernelN02700MinusP028BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP028Center2555‖ ≤ kernelN02700MinusP028Error2555 := by
  rw [kernelN02700MinusP028Exterior2555]
  norm_num [kernelN02700MinusP028Center2555, kernelN02700MinusP028Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP028DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP028Factor2555 * embedPair2542
          kernelN02700MinusP028Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP028Factor2555 : ℝ) * kernelN02700MinusP028Error2555
            := by
  rw [kernelN02700MinusP028Exterior2555]
  norm_num [kernelN02700MinusP028Factor2555, kernelN02700MinusP028Center2555,
      kernelN02700MinusP028Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

def kernelN02700MinusP029Center2555 : RatPair2542 := (0, 0)

def kernelN02700MinusP029Factor2555 : RatPair2542 := (0, 0)

noncomputable def kernelN02700MinusP029Error2555 : ℝ := 0

theorem kernelN02700MinusP029Exterior2555 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN02700MinusPosition2555 =
        0
        := by
  have hx : storedWidth ⟨29, by omega⟩ ^ 2 ≤ |kernelN02700MinusPosition2555| := by
    norm_num [storedWidth, kernelN02700MinusPosition2555]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
    (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx

theorem kernelN02700MinusP029BaseError2555 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP029Center2555‖ ≤ kernelN02700MinusP029Error2555 := by
  rw [kernelN02700MinusP029Exterior2555]
  norm_num [kernelN02700MinusP029Center2555, kernelN02700MinusP029Error2555,
      kernelN02700MinusZero2555]

theorem kernelN02700MinusP029DerivativeError2555 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ kernelN02700MinusPosition2555
        -
      embedPair2542 kernelN02700MinusP029Factor2555 * embedPair2542
          kernelN02700MinusP029Center2555‖ ≤
        (pairMagnitude2542 kernelN02700MinusP029Factor2555 : ℝ) * kernelN02700MinusP029Error2555
            := by
  rw [kernelN02700MinusP029Exterior2555]
  norm_num [kernelN02700MinusP029Factor2555, kernelN02700MinusP029Center2555,
      kernelN02700MinusP029Error2555, kernelN02700MinusZero2555, pairMagnitude2542]

theorem kernelN02700MinusGrid2555 :
    -stripRadius2303 + (2700 : ℝ) * (2 * stripRadius2303 / 10240) =
      kernelN02700MinusPosition2555 := by
  norm_num [stripRadius2303, kernelN02700MinusPosition2555]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.kernelN02700MinusP000DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP001DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP002DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP003DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP004DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP005DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP006DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP007DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP008DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP009DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP010DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP011DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP012DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP013DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP014DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP015DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP016DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP017DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP018DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP019DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP020DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP021DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP022DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP023DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP024DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP025DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP026DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP027DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP028DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusP029DerivativeError2555
#print axioms ConnesWeilRH.Dev.kernelN02700MinusGrid2555
