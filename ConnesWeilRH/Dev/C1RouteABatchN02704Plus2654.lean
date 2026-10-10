import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchN02704PlusPosition2654 : ℝ := (((-9895936151) : ℝ) /
        3200000000)

theorem batchN02704PlusZero2654 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchN02704PlusP000Center2654 : RatPair2542 := (0, 0)

def batchN02704PlusP000Factor2654 : RatPair2542 := (0, 0)

noncomputable def batchN02704PlusP000Error2654 : ℝ := 0

theorem batchN02704PlusP000Exterior2654 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02704PlusPosition2654 = 0
        := by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |batchN02704PlusPosition2654| := by
    norm_num [storedWidth, batchN02704PlusPosition2654]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem batchN02704PlusP000BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP000Center2654‖ ≤ batchN02704PlusP000Error2654 := by
  rw [batchN02704PlusP000Exterior2654]
  norm_num [batchN02704PlusP000Center2654, batchN02704PlusP000Error2654, batchN02704PlusZero2654]

theorem batchN02704PlusP000DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP000Factor2654 * embedPair2542 batchN02704PlusP000Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP000Factor2654 : ℝ) * batchN02704PlusP000Error2654 := by
  rw [batchN02704PlusP000Exterior2654]
  norm_num [batchN02704PlusP000Factor2654, batchN02704PlusP000Center2654,
      batchN02704PlusP000Error2654,
      batchN02704PlusZero2654, pairMagnitude2542]

def batchN02704PlusP001Input2654 : RatPair2542 := ((((-((21 * 10^40
        + 2590665986622484827322845344600412856161) * 10^40
        + 1339369612967568308599015150185097693111)) : ℚ) /
        ((59 * 10^40
        + 5965149429887586107108459481843895661464) * 10^40
        + 568333469734220561590691302604800000000)),
    ((54668031270047913913566379 : ℚ) /
        230584300921369395200000000))

def batchN02704PlusP001Center2654 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN02704PlusP001Factor2654 : RatPair2542 := ((((((((((((((2809018804924 * 10^40
        + 6555014566864310216405888637885388793967) * 10^40
        + 561948212701672226367893281957777813815) * 10^40
        + 2149397436794280422581886983205861526285) * 10^40
        + 3317275015299587004490216096108834913370) * 10^40
        + 7065519116778253761854633058305160288690) * 10^40
        + 4676139943505220246166248420101173330269) * 10^40
        + 2705032107559535403384629439012081921994) * 10^40
        + 47096127349566546412282667182381182690) * 10^40
        + 5987461108987265824246821965201916747224) * 10^40
        + 4096776237969781532533082650509366488834) * 10^40
        + 3422445460311254450356333754208166518853) : ℚ) /
        (((((((((((14337 * 10^40
        + 5571624924703064179895492909657341405928) * 10^40
        + 1113600893697700538642812875845270330342) * 10^40
        + 1537764969440524034745049923841587449606) * 10^40
        + 1216863532233906723483350873129350130997) * 10^40
        + 6074745595601470270645852374359760010264) * 10^40
        + 6110529882116449832403661278014303419814) * 10^40
        + 8399469789364094466253178433858029982958) * 10^40
        + 2767200214061251555046555324774647858419) * 10^40
        + 6522085635056742841348454438905597854559) * 10^40
        + 4761764934940637151390906473823640892853) * 10^40
        + 6255942376144816918661836907666995150848)),
    (((-((((((((12354523 * 10^40
        + 3728542207420894276860545965078898222712) * 10^40
        + 3963786114363025239742393350697861306926) * 10^40
        + 3771788163348248882469013925723160523550) * 10^40
        + 801553900672647493038115255789174900302) * 10^40
        + 3758396620629135965535149092060173624141) * 10^40
        + 1096387366466101917972532904672614845694) * 10^40
        + 3917609550979057075037564855399904718061) * 10^40
        + 4611038503806989005925624072684670978283)) : ℚ) /
        (((((((3050093163439907082370504546418905483763 * 10^40
        + 12627471688809529625630990196760447195) * 10^40
        + 4408035631287601163648154772370580682660) * 10^40
        + 9763374694818108913849149985740546032921) * 10^40
        + 895785634565358934712351272341632371431) * 10^40
        + 7266286930266086384385654927261912752636) * 10^40
        + 4652652587857820583710152832941835075799) * 10^40
        + 9338010115055769106750420158131503890432)))

noncomputable def batchN02704PlusP001Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP001BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP001Center2654‖ ≤ batchN02704PlusP001Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP001Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP001Input2654]
  have hs : compactExp2547 batchN02704PlusP001Input2654 9 =
      (batchN02704PlusP001Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP001Input2654 9).2 : ℝ) = batchN02704PlusP001Error2654
      := by
    rw [hs]
    norm_num [batchN02704PlusP001Error2654]
  have h := compactExp_error2547 batchN02704PlusP001Input2654 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          batchN02704PlusP001Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP001Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP001DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP001Factor2654 * embedPair2542 batchN02704PlusP001Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP001Factor2654 : ℝ) * batchN02704PlusP001Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP001Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP001Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP001BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP001Factor2654)

def batchN02704PlusP002Input2654 : RatPair2542 := ((((-((564 * 10^40
        + 6320295773356197331617375810041260089035) * 10^40
        + 1909897556892439653628817325904678324151)) : ℚ) /
        ((2298 * 10^40
        + 4999305507355519060301944907893290580952) * 10^40
        + 3852905515627880742725530420838400000000)),
    (((-54668031270047913913566379) : ℚ) /
        115292150460684697600000000))

def batchN02704PlusP002Center2654 : RatPair2542 := ((((-150665789589046507317) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-646605045251160912061) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN02704PlusP002Factor2654 : RatPair2542 := ((((-(((((((((((388512730594602611427 * 10^40
        + 4612333653181405059180001122698834429274) * 10^40
        + 9497048405723652849155598561809048034830) * 10^40
        + 9186874812747120875144297898984495285300) * 10^40
        + 1381825895163784084575405657150479655820) * 10^40
        + 1981811841111232855445129615020691134911) * 10^40
        + 9329424724861337649173507820653380988865) * 10^40
        + 8677569194863815483914730726246361889830) * 10^40
        + 1642174045735364798676224539011620580004) * 10^40
        + 5268493135878149905298875983709750416268) * 10^40
        + 4621478458594663584486734072063746828147) * 10^40
        + 5239619609651917892220770496992545693627)) : ℚ) /
        (((((((((((3019930317616973 * 10^40
        + 4524317028288467701992012581616915238687) * 10^40
        + 9391684448924957697766618220334382849412) * 10^40
        + 4191609330842639799675908688248402087461) * 10^40
        + 1384709180257514436822917652155225256707) * 10^40
        + 6929276930442972944260433155273209803446) * 10^40
        + 2404658420800639149916729294945010070224) * 10^40
        + 7134691835352195256051105861424317399089) * 10^40
        + 5837231512502219880711745939751295971304) * 10^40
        + 5441177725985241316569094628178134214019) * 10^40
        + 4457651911830410445571197604787536392426) * 10^40
        + 1060527240700634952391901233716729479168)),
    ((((((((((1495668136259 * 10^40
        + 6988717899217234422200088929845303396481) * 10^40
        + 9767420700060061719542004150687420066400) * 10^40
        + 8801018564727157871197156868060966606050) * 10^40
        + 6704473276007170594776756892967924086289) * 10^40
        + 6462849648298473500016728036514794496122) * 10^40
        + 9990028142836282520488465447206390398221) * 10^40
        + 4996511456204109056286071858159369176814) * 10^40
        + 4825682256807080554675943855877262051563) : ℚ) /
        ((((((((10797609 * 10^40
        + 3586473984077732042708049114296486875524) * 10^40
        + 8970281936486609936035964207494624051236) * 10^40
        + 529955905854364300751554222584167967660) * 10^40
        + 44383336432906145944076110436688860061) * 10^40
        + 1615565763272992491422655305589112821870) * 10^40
        + 8825999741868268631751715784150425484683) * 10^40
        + 8633339624263947002089039881294027246696) * 10^40
        + 1172664106250138656450683306238963351552)))

noncomputable def batchN02704PlusP002Error2654 : ℝ := ((2703320551278323549 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP002BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP002Center2654‖ ≤ batchN02704PlusP002Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP002Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP002Input2654]
  have hs : compactExp2547 batchN02704PlusP002Input2654 8 =
      (batchN02704PlusP002Center2654, ((2703320551278323549 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP002Input2654 8).2 : ℝ) = batchN02704PlusP002Error2654
      := by
    rw [hs]
    norm_num [batchN02704PlusP002Error2654]
  have h := compactExp_error2547 batchN02704PlusP002Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchN02704PlusP002Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP002Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP002DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP002Factor2654 * embedPair2542 batchN02704PlusP002Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP002Factor2654 : ℝ) * batchN02704PlusP002Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP002Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP002Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP002BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP002Factor2654)

def batchN02704PlusP003Input2654 : RatPair2542 := ((((-((75251 * 10^40
        + 1057389726409136056781964181355512754308) * 10^40
        + 182014849813444389447983162613849155677)) : ℚ) /
        ((415806 * 10^40
        + 9371244809296725772723606675176446357802) * 10^40
        + 447237920754980795911929244876800000000)),
    (((-54668031270047913913566379) : ℚ) /
        115292150460684697600000000))

def batchN02704PlusP003Center2654 : RatPair2542 := ((((-2337165949435292114676855823) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-10030301494560025509101554821) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN02704PlusP003Factor2654 : RatPair2542 :=
    ((((-(((((((((((187617394676694618357935375672911926
    *
    10^40
        + 2234604427589933770980684402442495293188) * 10^40
        + 8872429325647948094569173961065799391397) * 10^40
        + 8788286061632784954661928898538353108424) * 10^40
        + 5596565370935195268765934755361954733039) * 10^40
        + 8964338480339662268045749374606881030414) * 10^40
        + 5005154144937737911103622330221116835045) * 10^40
        + 4598447844638543409141653129097632386732) * 10^40
        + 1484083768205757283537411550190812908187) * 10^40
        + 1441444617388679995275494089507390372089) * 10^40
        + 7214224971931049389936905884369451469415) * 10^40
        + 3554626487993577213660536235752845842081)) : ℚ) /
        (((((((((((2857880730403380952553900572301 * 10^40
        + 6557237649446643897602694971267542583308) * 10^40
        + 3825313345203167274595822512313839383611) * 10^40
        + 9678649446994112681776548630744544047954) * 10^40
        + 7956000491841281685072851878699222863694) * 10^40
        + 1620611713558430814030835878137455449649) * 10^40
        + 1380260984564014137458479931631399435698) * 10^40
        + 5207371596965953272402474056159134634389) * 10^40
        + 1082950143690779550394286105770112399926) * 10^40
        + 5161074994618460419477583843648608443428) * 10^40
        + 9095513482536994545284352629893814726478) * 10^40
        + 5291811954076430771998000574126100578304)),
    (((-((((((((1262642994959002207949 * 10^40
        + 6390630256817199104031761676065003525706) * 10^40
        + 6601826125687847509698372663914716354960) * 10^40
        + 6372201775336685610774463896807913984926) * 10^40
        + 7471468672733997386181502824187329463787) * 10^40
        + 9298939583353847004356979690121707829482) * 10^40
        + 7948919774485734204408232548741255548593) * 10^40
        + 8700314883169219226907865380716627117769) * 10^40
        + 607251830978540195982291971287639630351)) : ℚ) /
        ((((((((34692676673811274 * 10^40
        + 128074125893813266840425590508825200511) * 10^40
        + 4088868557146161593343621828857606946430) * 10^40
        + 3116465880148502597479334338734333885453) * 10^40
        + 6690487160467244914226014038809137420893) * 10^40
        + 967985277916314488509526984022673398831) * 10^40
        + 1094247494220346831507178057090725668908) * 10^40
        + 4144132175624955449388270581627986533744) * 10^40
        + 5746016863812249415352748902068829290496)))

noncomputable def batchN02704PlusP003Error2654 : ℝ := ((39308232611829201955562319 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP003BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP003Center2654‖ ≤ batchN02704PlusP003Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP003Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP003Input2654]
  have hs : compactExp2547 batchN02704PlusP003Input2654 8 =
      (batchN02704PlusP003Center2654, ((39308232611829201955562319 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP003Input2654 8).2 : ℝ) = batchN02704PlusP003Error2654
      := by
    rw [hs]
    norm_num [batchN02704PlusP003Error2654]
  have h := compactExp_error2547 batchN02704PlusP003Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchN02704PlusP003Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP003Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP003DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP003Factor2654 * embedPair2542 batchN02704PlusP003Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP003Factor2654 : ℝ) * batchN02704PlusP003Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP003Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP003Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP003BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP003Factor2654)

def batchN02704PlusP004Input2654 : RatPair2542 := ((((-((1314 * 10^40
        + 3793291039928624094795639072353193421464) * 10^40
        + 9080182155977962095085629655006240824151)) : ℚ) /
        ((8382 * 10^40
        + 7530312459026314251984141299542600038641) * 10^40
        + 5318978297451200742725530420838400000000)),
    ((54668031270047913913566379 : ℚ) /
        115292150460684697600000000))

def batchN02704PlusP004Center2654 : RatPair2542 := ((((-2280774527693167736821574979679) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((2447072292770089851661591621051 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchN02704PlusP004Factor2654 : RatPair2542 := ((((-(((((((((((248871592864472585438146 *
    10^40
        + 4429903386571098165524616921249608709502) * 10^40
        + 1491305787396749264963531381049379940902) * 10^40
        + 9339591491596066161538776995625150416530) * 10^40
        + 552818183849932992856742459895596941915) * 10^40
        + 8014937676080655564056358511561772809651) * 10^40
        + 1795178364992019435896767218530176153468) * 10^40
        + 2639345016233696445240019817314777577953) * 10^40
        + 6834096637727202704646109221974211579157) * 10^40
        + 8570541347196207088783737979757013171411) * 10^40
        + 6153508969494974820248256558328823939880) * 10^40
        + 8280745533073230191362597791914420693627)) : ℚ) /
        (((((((((((7106405422715299650 * 10^40
        + 9736496649402725534469439527879491179717) * 10^40
        + 3838930789879873260373298956223895462963) * 10^40
        + 8225280078693771444232931461713551566460) * 10^40
        + 6506022864718155662185846416708969955773) * 10^40
        + 2890171178197773450034577446036887587024) * 10^40
        + 4523940870746477384389076075139594105497) * 10^40
        + 3220925892413394983938660744868480430508) * 10^40
        + 4732686584093000672416587865704527781048) * 10^40
        + 1626514542923533945509805206213686110875) * 10^40
        + 2326137382286809902288121467769545857206) * 10^40
        + 3238873731322371627310301233716729479168)),
    ((((((((((103483159285232 * 10^40
        + 4674718276171023883152218837109149144438) * 10^40
        + 9750532584124223846652825950392699635324) * 10^40
        + 8486793381568514881110519063962229307927) * 10^40
        + 5875655499652024464054130593797160453591) * 10^40
        + 1552699765134112306264801930742206965262) * 10^40
        + 4342137460219603053045700050550389008590) * 10^40
        + 3307605948380851809338097455706816272794) * 10^40
        + 6014715209576214523732822843341487948437) : ℚ) /
        ((((((((1910276868 * 10^40
        + 7143605086617080012378433395487729694547) * 10^40
        + 9380410139889950991794641576550999617111) * 10^40
        + 1319557373781176227134621714215647026550) * 10^40
        + 6747846133431990198624640516214316470816) * 10^40
        + 4819251154708896951614326628589582303542) * 10^40
        + 1989429138044381900918670741501429345974) * 10^40
        + 5801300267448362710470076006840776150972) * 10^40
        + 8336703345951134713129083306238963351552)))

noncomputable def batchN02704PlusP004Error2654 : ℝ := ((18721683894319600454709178461 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP004BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP004Center2654‖ ≤ batchN02704PlusP004Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP004Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP004Input2654]
  have hs : compactExp2547 batchN02704PlusP004Input2654 8 =
      (batchN02704PlusP004Center2654, ((18721683894319600454709178461 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP004Input2654 8).2 : ℝ) = batchN02704PlusP004Error2654
      := by
    rw [hs]
    norm_num [batchN02704PlusP004Error2654]
  have h := compactExp_error2547 batchN02704PlusP004Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchN02704PlusP004Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP004Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP004DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP004Factor2654 * embedPair2542 batchN02704PlusP004Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP004Factor2654 : ℝ) * batchN02704PlusP004Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP004Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP004Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP004BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP004Factor2654)

def batchN02704PlusP005Center2654 : RatPair2542 := (0, 0)

def batchN02704PlusP005Factor2654 : RatPair2542 := (0, 0)

noncomputable def batchN02704PlusP005Error2654 : ℝ := 0

theorem batchN02704PlusP005Exterior2654 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02704PlusPosition2654 = 0
        := by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |batchN02704PlusPosition2654| := by
    norm_num [storedWidth, batchN02704PlusPosition2654]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem batchN02704PlusP005BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP005Center2654‖ ≤ batchN02704PlusP005Error2654 := by
  rw [batchN02704PlusP005Exterior2654]
  norm_num [batchN02704PlusP005Center2654, batchN02704PlusP005Error2654, batchN02704PlusZero2654]

theorem batchN02704PlusP005DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP005Factor2654 * embedPair2542 batchN02704PlusP005Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP005Factor2654 : ℝ) * batchN02704PlusP005Error2654 := by
  rw [batchN02704PlusP005Exterior2654]
  norm_num [batchN02704PlusP005Factor2654, batchN02704PlusP005Center2654,
      batchN02704PlusP005Error2654,
      batchN02704PlusZero2654, pairMagnitude2542]

def batchN02704PlusP006Input2654 : RatPair2542 := ((((-10703175194025607899013599449683) : ℚ) /
        17997946250671801739673600000000),
    ((0 : ℚ) /
        1))

def batchN02704PlusP006Center2654 : RatPair2542 := (((638567541572489 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def batchN02704PlusP006Factor2654 : RatPair2542 := ((((((8293 * 10^40
        + 6867861365139266520441566476783747349244) * 10^40
        + 8293594240364391287298319070610565544197) * 10^40
        + 6823910093817250835697018970756779917363) : ℚ) /
        ((242913578760400323024283657905529282089 * 10^40
        + 273103668815392236120585583293744315861) * 10^40
        + 4130620045995286685576151766054239338904)),
    ((0 : ℚ) /
        1))

noncomputable def batchN02704PlusP006Error2654 : ℝ := ((2524797428367 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP006BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP006Center2654‖ ≤ batchN02704PlusP006Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP006Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP006Input2654]
  have hs : compactExp2547 batchN02704PlusP006Input2654 7 =
      (batchN02704PlusP006Center2654, ((2524797428367 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP006Input2654 7).2 : ℝ) = batchN02704PlusP006Error2654
      := by
    rw [hs]
    norm_num [batchN02704PlusP006Error2654]
  have h := compactExp_error2547 batchN02704PlusP006Input2654 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          batchN02704PlusP006Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP006Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP006DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP006Factor2654 * embedPair2542 batchN02704PlusP006Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP006Factor2654 : ℝ) * batchN02704PlusP006Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP006Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP006Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP006BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP006Factor2654)

def batchN02704PlusP007Input2654 : RatPair2542 := ((((-((75251 * 10^40
        + 1057389726409136056781964181355512754308) * 10^40
        + 182014849813444389447983162613849155677)) : ℚ) /
        ((103951 * 10^40
        + 7342811202324181443180901668794111589450) * 10^40
        + 5111809480188745198977982311219200000000)),
    ((0 : ℚ) /
        1))

def batchN02704PlusP007Center2654 : RatPair2542 := (((11065998679404049300331925531 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN02704PlusP007Factor2654 : RatPair2542 := ((((((((((((((1519976 * 10^40
        + 8623105096138561505094934813882737269937) * 10^40
        + 4350569921380503627967004500723697567137) * 10^40
        + 7216672134718132698803556130391302076606) * 10^40
        + 8723061562387590904928298893379303964607) * 10^40
        + 429910099301819758700555405949163633013) * 10^40
        + 716783620306766167664113296469856420676) * 10^40
        + 7323918393686806421260547074362234768638) * 10^40
        + 4008524913477588729360856395124542932813) * 10^40
        + 2559564259382330725109972344465480165678) * 10^40
        + 1930693213797826595956947021176627096553) * 10^40
        + 6653160036129659882342079647225613539603) : ℚ) /
        (((((((((((577 * 10^40
        + 1444172799225582513338373249956402873339) * 10^40
        + 4071411590215724113134186346326236162880) * 10^40
        + 3316721751865119791243164614600706729736) * 10^40
        + 9494839572299008610955103857997467330461) * 10^40
        + 841882898346179248276484986527296832351) * 10^40
        + 7190351194684217779443427090949683888072) * 10^40
        + 1308434248793225592158093328191255050696) * 10^40
        + 8535640839120091984933127861606192128614) * 10^40
        + 7748690584172490980035377552430103230934) * 10^40
        + 7210189081089400554746657968816811789457) * 10^40
        + 9747648289037279058736637177804908316824)),
    ((0 : ℚ) /
        1))

noncomputable def batchN02704PlusP007Error2654 : ℝ := ((803023130034719983008463 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN02704PlusP007BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP007Center2654‖ ≤ batchN02704PlusP007Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP007Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP007Input2654]
  have hs : compactExp2547 batchN02704PlusP007Input2654 6 =
      (batchN02704PlusP007Center2654, ((803023130034719983008463 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP007Input2654 6).2 : ℝ) = batchN02704PlusP007Error2654
      := by
    rw [hs]
    norm_num [batchN02704PlusP007Error2654]
  have h := compactExp_error2547 batchN02704PlusP007Input2654 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          batchN02704PlusP007Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP007Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP007DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP007Factor2654 * embedPair2542 batchN02704PlusP007Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP007Factor2654 : ℝ) * batchN02704PlusP007Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP007Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP007Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP007BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP007Factor2654)

def batchN02704PlusP008Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((39371688844277275851267847 : ℚ) /
        14757395258967641292800000000))

def batchN02704PlusP008Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP008Factor2654 : RatPair2542 :=
    ((((((((((((((1206759086290854834077255647761234 *
    10^40
        + 4183742987607591163548232908971119593416) * 10^40
        + 604054155999615797777624517805745563614) * 10^40
        + 9447074027002205339769001363954611949169) * 10^40
        + 9909169473712027882036082958690035693789) * 10^40
        + 9884474867020162655286540324936143316845) * 10^40
        + 1445596552665301220845954789275485199895) * 10^40
        + 2857748671405836572777904047150758952343) * 10^40
        + 7795194564642496654478117419368878988583) * 10^40
        + 4144745222540501836153778246151631028666) * 10^40
        + 2349217647066591139032992826310899101820) * 10^40
        + 2345653898747474441451020976962338040071) : ℚ) /
        (((((((((((216847422952611 * 10^40
        + 9853297037345433200032085497698473566414) * 10^40
        + 4876155849812321025163157314371284765972) * 10^40
        + 2360215720430918030683573008919214833686) * 10^40
        + 4901419599211119074242512487431316976335) * 10^40
        + 4487894102956750297507543878956507037716) * 10^40
        + 7400154525084361633755339551735298891805) * 10^40
        + 910829997049874445642027387798146725633) * 10^40
        + 3973741111606932121715002271087584457401) * 10^40
        + 1096987919330530654408592902387151852231) * 10^40
        + 2066901502085934789780292701940491804083) * 10^40
        + 4519776551428411829204162296504402313216)),
    (((-((((((((37561688951878620898 * 10^40
        + 3964902245780691762603812585263556948937) * 10^40
        + 3470655549798057877235374926833036314783) * 10^40
        + 7896789141657755372117567264854845608798) * 10^40
        + 2560349993540419096340652552586956680636) * 10^40
        + 370208887768174259233372912258529348485) * 10^40
        + 5647601890939236434419030748490333163294) * 10^40
        + 9665621821626831411860559523090523618072) * 10^40
        + 1632076358393993670557225044297275321019)) : ℚ) /
        ((((((((282009 * 10^40
        + 1534053747890721878994883316071335516412) * 10^40
        + 7203412894862525178913122632293423961325) * 10^40
        + 4643598740483511798171907167314555273299) * 10^40
        + 7653370293239890248041392433252686320301) * 10^40
        + 276787278843864065217788346412891156313) * 10^40
        + 3804230123880309267720806057899489492219) * 10^40
        + 4660536509913901103997583397664676183943) * 10^40
        + 4148980184670273661267873030935804903424)))

noncomputable def batchN02704PlusP008Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP008BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP008Center2654‖ ≤ batchN02704PlusP008Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP008Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP008Input2654]
  have hs : compactExp2547 batchN02704PlusP008Input2654 14 =
      (batchN02704PlusP008Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP008Input2654 14).2 : ℝ) =
      batchN02704PlusP008Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP008Error2654]
  have h := compactExp_error2547 batchN02704PlusP008Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP008Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP008Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP008DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP008Factor2654 * embedPair2542 batchN02704PlusP008Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP008Factor2654 : ℝ) * batchN02704PlusP008Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP008Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP008Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP008BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP008Factor2654)

def batchN02704PlusP009Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((58556016847187164876286361 : ℚ) /
        14757395258967641292800000000))

def batchN02704PlusP009Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP009Factor2654 : RatPair2542 :=
    ((((((((((((((1206759086011652630630062188134081 *
    10^40
        + 3900390706201996770724705284611321509715) * 10^40
        + 5627058796216335705009873316324539386695) * 10^40
        + 1409092734171796466818610411793679632623) * 10^40
        + 9792125438728134938506575620300912986377) * 10^40
        + 2810787009771290346028649380281057968558) * 10^40
        + 6352203725277795224956777130485963738786) * 10^40
        + 8113404424399135903679877973215427172144) * 10^40
        + 6371698785235561876063964898098781932712) * 10^40
        + 1003088139042146841234770983657659879272) * 10^40
        + 350137601710383322108910195197316703156) * 10^40
        + 4563908528083173663695137106209950110663) : ℚ) /
        (((((((((((216847422952611 * 10^40
        + 9853297037345433200032085497698473566414) * 10^40
        + 4876155849812321025163157314371284765972) * 10^40
        + 2360215720430918030683573008919214833686) * 10^40
        + 4901419599211119074242512487431316976335) * 10^40
        + 4487894102956750297507543878956507037716) * 10^40
        + 7400154525084361633755339551735298891805) * 10^40
        + 910829997049874445642027387798146725633) * 10^40
        + 3973741111606932121715002271087584457401) * 10^40
        + 1096987919330530654408592902387151852231) * 10^40
        + 2066901502085934789780292701940491804083) * 10^40
        + 4519776551428411829204162296504402313216)),
    (((-((((((((130349503150386209376 * 10^40
        + 8442568006201604471815771887908883481155) * 10^40
        + 8984667236712791302288139680085571185112) * 10^40
        + 9217114153196867034167668401349659883671) * 10^40
        + 9602695106321272494472860278571229123832) * 10^40
        + 94155804034023481441714767377071558740) * 10^40
        + 3249029587661782143334117275308781015671) * 10^40
        + 4263446302499505911307073876124743089128) * 10^40
        + 1240943410722156398847746821776809380481)) : ℚ) /
        ((((((((658021 * 10^40
        + 3579458745078351050988061070833116204963) * 10^40
        + 141296754679225417463952808684655909759) * 10^40
        + 4168397061128194195734450057067295637699) * 10^40
        + 4524530684226410578763249010922934747369) * 10^40
        + 645836983969016152174839474963412698064) * 10^40
        + 5543203622387388291348547468432142148512) * 10^40
        + 874585189799102575994361261217577762534) * 10^40
        + 6347620430897305209625037072183544774656)))

noncomputable def batchN02704PlusP009Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP009BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP009Center2654‖ ≤ batchN02704PlusP009Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP009Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP009Input2654]
  have hs : compactExp2547 batchN02704PlusP009Input2654 14 =
      (batchN02704PlusP009Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP009Input2654 14).2 : ℝ) =
      batchN02704PlusP009Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP009Error2654]
  have h := compactExp_error2547 batchN02704PlusP009Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP009Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP009Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP009DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP009Factor2654 * embedPair2542 batchN02704PlusP009Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP009Factor2654 : ℝ) * batchN02704PlusP009Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP009Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP009Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP009BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP009Factor2654)

def batchN02704PlusP010Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((34833351639308188388476671 : ℚ) /
        7378697629483820646400000000))

def batchN02704PlusP010Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP010Factor2654 : RatPair2542 := ((((((((((((((301689771449981858199991910493640
    *
    10^40
        + 6693209091458090104567922028158567879806) * 10^40
        + 2086700561667100387447102144376804335390) * 10^40
        + 6757829419206705422045140173558509719236) * 10^40
        + 2154557439514190657486180806527468722444) * 10^40
        + 6122996909330383989428782547073806019432) * 10^40
        + 345393275797277670616532104444267715635) * 10^40
        + 2424933432041577785209404242083361627844) * 10^40
        + 5007713078243491334635021367701831490188) * 10^40
        + 2375464081021286193695076590737126322947) * 10^40
        + 7909853430688990903084189651417237176705) * 10^40
        + 188629458988536437913102094058259662519) : ℚ) /
        (((((((((((54211855738152 * 10^40
        + 9963324259336358300008021374424618391603) * 10^40
        + 6219038962453080256290789328592821191493) * 10^40
        + 590053930107729507670893252229803708421) * 10^40
        + 6225354899802779768560628121857829244083) * 10^40
        + 8621973525739187574376885969739126759429) * 10^40
        + 1850038631271090408438834887933824722951) * 10^40
        + 2727707499262468611410506846949536681408) * 10^40
        + 3493435277901733030428750567771896114350) * 10^40
        + 2774246979832632663602148225596787963057) * 10^40
        + 8016725375521483697445073175485122951020) * 10^40
        + 8629944137857102957301040574126100578304)),
    (((-((((((((2153925194498109048 * 10^40
        + 2160038041739955963726550302542601027922) * 10^40
        + 7183076614454201814307239032859031737370) * 10^40
        + 5264745116813711998353037403577232902148) * 10^40
        + 5559167032982764887822457775271133108442) * 10^40
        + 8659744720326937104353110404296977726956) * 10^40
        + 4984668971560173946926735942643558128989) * 10^40
        + 6982967645825494737323937409513662447857) * 10^40
        + 921155630447361963551904699832049469263)) : ℚ) /
        ((((((((9139 * 10^40
        + 1855270260348310431263723070428237725068) * 10^40
        + 9307518010481655908575888233453953554302) * 10^40
        + 2141227736960113808274089584125934661634) * 10^40
        + 7146174037280922369149489569596151871491) * 10^40
        + 2370081069221791891002428326041158509695) * 10^40
        + 3410322272533158170713174270394890863173) * 10^40
        + 7789924794302765313555477239739133024479) * 10^40
        + 6477050283762462572355903292669215899648)))

noncomputable def batchN02704PlusP010Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP010BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP010Center2654‖ ≤ batchN02704PlusP010Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP010Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP010Input2654]
  have hs : compactExp2547 batchN02704PlusP010Input2654 14 =
      (batchN02704PlusP010Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP010Input2654 14).2 : ℝ) =
      batchN02704PlusP010Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP010Error2654]
  have h := compactExp_error2547 batchN02704PlusP010Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP010Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP010Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP010DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP010Factor2654 * embedPair2542 batchN02704PlusP010Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP010Factor2654 : ℝ) * batchN02704PlusP010Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP010Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP010Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP010BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP010Factor2654)

def batchN02704PlusP011Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((38537265293058906320467951 : ℚ) /
        7378697629483820646400000000))

def batchN02704PlusP011Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP011Factor2654 : RatPair2542 := ((((((((((((((301689771409594104867990572556260
    *
    10^40
        + 343047085466447279247825843176720448821) * 10^40
        + 2213930553151054887390392582690778157103) * 10^40
        + 45861992910241087606703320495273197682) * 10^40
        + 2874504234766402947267430096953241294468) * 10^40
        + 7741204064471199642185057693109282906085) * 10^40
        + 9686645178038357027855942403297446911219) * 10^40
        + 1349738520891446286480568119887473795367) * 10^40
        + 7983845956117386822881361347195012208358) * 10^40
        + 3283280733716363309885531579805767144177) * 10^40
        + 6649539519624520354607737479752284005179) * 10^40
        + 2688696716196553825363133743325802301079) : ℚ) /
        (((((((((((54211855738152 * 10^40
        + 9963324259336358300008021374424618391603) * 10^40
        + 6219038962453080256290789328592821191493) * 10^40
        + 590053930107729507670893252229803708421) * 10^40
        + 6225354899802779768560628121857829244083) * 10^40
        + 8621973525739187574376885969739126759429) * 10^40
        + 1850038631271090408438834887933824722951) * 10^40
        + 2727707499262468611410506846949536681408) * 10^40
        + 3493435277901733030428750567771896114350) * 10^40
        + 2774246979832632663602148225596787963057) * 10^40
        + 8016725375521483697445073175485122951020) * 10^40
        + 8629944137857102957301040574126100578304)),
    (((-((((((((64339844827495091759 * 10^40
        + 5114955263062663346155771608166277791233) * 10^40
        + 9476486279337593046573693261055848627688) * 10^40
        + 3868083448009674267951491347249479681276) * 10^40
        + 9835002879742975595151554533285586027123) * 10^40
        + 2531860960325180182244391395743767101981) * 10^40
        + 3857303882386178881701286591788770789127) * 10^40
        + 8898803281260700526259693167643803346215) * 10^40
        + 617139365810229692632993955730503628101)) : ℚ) /
        ((((((((246758 * 10^40
        + 92297029404381644120522901562418576861) * 10^40
        + 1302986283004709531548982303256745966159) * 10^40
        + 7813148897923072823400418771400235864137) * 10^40
        + 2946699006584903967036218379096100530263) * 10^40
        + 3992188868988381057065564803111279761774) * 10^40
        + 2078701358395270609255705300662053305692) * 10^40
        + 327969446174663465997885472956591660950) * 10^40
        + 4880357661586489453609388902068829290496)))

noncomputable def batchN02704PlusP011Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP011BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP011Center2654‖ ≤ batchN02704PlusP011Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP011Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP011Input2654]
  have hs : compactExp2547 batchN02704PlusP011Input2654 14 =
      (batchN02704PlusP011Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP011Input2654 14).2 : ℝ) =
      batchN02704PlusP011Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP011Error2654]
  have h := compactExp_error2547 batchN02704PlusP011Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP011Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP011Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP011DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP011Factor2654 * embedPair2542 batchN02704PlusP011Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP011Factor2654 : ℝ) * batchN02704PlusP011Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP011Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP011Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP011BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP011Factor2654)

def batchN02704PlusP012Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((847472267017150096839859 : ℚ) /
        147573952589676412928000000))

def batchN02704PlusP012Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP012Factor2654 : RatPair2542 := ((((((((((((((75422442840865810179414070452267
    *
    10^40
        + 8883874941427771880416222095606178370584) * 10^40
        + 6148822427282070427307770497096008933194) * 10^40
        + 1423949234684294567912118528563166347818) * 10^40
        + 4759449923308541580169578262968041787165) * 10^40
        + 2128149082996775776731297036640674843708) * 10^40
        + 2316822215384799243920372305158894790783) * 10^40
        + 2369230873843823303570949148523307207207) * 10^40
        + 8021228721152187843209160012697082727968) * 10^40
        + 7597733306722391456669228157685821925390) * 10^40
        + 9015599935553660213148438810197862915913) * 10^40
        + 5664214360120315034694065699193957812447) : ℚ) /
        (((((((((((13552963934538 * 10^40
        + 2490831064834089575002005343606154597900) * 10^40
        + 9054759740613270064072697332148205297873) * 10^40
        + 2647513482526932376917723313057450927105) * 10^40
        + 4056338724950694942140157030464457311020) * 10^40
        + 9655493381434796893594221492434781689857) * 10^40
        + 2962509657817772602109708721983456180737) * 10^40
        + 8181926874815617152852626711737384170352) * 10^40
        + 873358819475433257607187641942974028587) * 10^40
        + 5693561744958158165900537056399196990764) * 10^40
        + 4504181343880370924361268293871280737755) * 10^40
        + 2157486034464275739325260143531525144576)),
    (((-((((((((8843101887860195047 * 10^40
        + 9614063074556696466738527429957647206746) * 10^40
        + 5698792584475438337922995167698605587208) * 10^40
        + 1797619776114263892278917793192772342489) * 10^40
        + 9540702783353991622852428715431883346432) * 10^40
        + 8386835931388061439983885218297079523554) * 10^40
        + 1980121493784282560553742699014563016126) * 10^40
        + 6655075448342803765447198867904083565193) * 10^40
        + 5181587667027720553904372328296267348225)) : ℚ) /
        ((((((((30844 * 10^40
        + 7511537128675547705515065362695302322107) * 10^40
        + 6412873285375588691443622787907093245769) * 10^40
        + 9726643612240384102925052346425029483017) * 10^40
        + 1618337375823112995879527297387012566282) * 10^40
        + 9249023608623547632133195600388909970221) * 10^40
        + 7759837669799408826156963162582756663211) * 10^40
        + 5040996180771832933249735684119573957618) * 10^40
        + 8110044707698311181701173612758603661312)))

noncomputable def batchN02704PlusP012Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP012BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP012Center2654‖ ≤ batchN02704PlusP012Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP012Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP012Input2654]
  have hs : compactExp2547 batchN02704PlusP012Input2654 14 =
      (batchN02704PlusP012Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP012Input2654 14).2 : ℝ) =
      batchN02704PlusP012Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP012Error2654]
  have h := compactExp_error2547 batchN02704PlusP012Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP012Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP012Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP012DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP012Factor2654 * embedPair2542 batchN02704PlusP012Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP012Factor2654 : ℝ) * batchN02704PlusP012Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP012Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP012Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP012BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP012Factor2654)

def batchN02704PlusP013Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((9173924387612369119306941 : ℚ) /
        1475739525896764129280000000))

def batchN02704PlusP013Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP013Factor2654 : RatPair2542 := ((((((((((((((301689771317615220850064425200561
    *
    10^40
        + 4875056212499807973985232294396066434089) * 10^40
        + 6317655165634836491496538360010085748489) * 10^40
        + 9795544633447493949818343703462662995835) * 10^40
        + 3648197945106160524881000824141422918605) * 10^40
        + 8141364530553861504583903269837594592293) * 10^40
        + 699213008258075472711495135784192874980) * 10^40
        + 3425167269880593245727340321876544141733) * 10^40
        + 9462433926594147365820349096397526328692) * 10^40
        + 7188171033258805783121546911287846966980) * 10^40
        + 9301952438171973511511120854930741562751) * 10^40
        + 8869491071443165380186032978262480799063) : ℚ) /
        (((((((((((54211855738152 * 10^40
        + 9963324259336358300008021374424618391603) * 10^40
        + 6219038962453080256290789328592821191493) * 10^40
        + 590053930107729507670893252229803708421) * 10^40
        + 6225354899802779768560628121857829244083) * 10^40
        + 8621973525739187574376885969739126759429) * 10^40
        + 1850038631271090408438834887933824722951) * 10^40
        + 2727707499262468611410506846949536681408) * 10^40
        + 3493435277901733030428750567771896114350) * 10^40
        + 2774246979832632663602148225596787963057) * 10^40
        + 8016725375521483697445073175485122951020) * 10^40
        + 8629944137857102957301040574126100578304)),
    (((-((((((((25527190675033818353 * 10^40
        + 7778854185383988342017150099365522542726) * 10^40
        + 3923883319582345114511756209054868473213) * 10^40
        + 224839550894081751661722364430699747998) * 10^40
        + 8359796919366950659535737177582131912016) * 10^40
        + 1431870621554100872257007378104188064741) * 10^40
        + 3353543494299240996719347267962679354312) * 10^40
        + 984303168009772830236237256964995492718) * 10^40
        + 4189572001741172387173443005863466840265)) : ℚ) /
        ((((((((82252 * 10^40
        + 6697432343134793881373507633854139525620) * 10^40
        + 3767662094334903177182994101085581988719) * 10^40
        + 9271049632641024274466806257133411954712) * 10^40
        + 4315566335528301322345406126365366843421) * 10^40
        + 1330729622996127019021854934370426587258) * 10^40
        + 692900452798423536418568433554017768564) * 10^40
        + 109323148724887821999295157652197220316) * 10^40
        + 8293452553862163151203129634022943096832)))

noncomputable def batchN02704PlusP013Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP013BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP013Center2654‖ ≤ batchN02704PlusP013Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP013Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP013Input2654]
  have hs : compactExp2547 batchN02704PlusP013Input2654 14 =
      (batchN02704PlusP013Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP013Input2654 14).2 : ℝ) =
      batchN02704PlusP013Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP013Error2654]
  have h := compactExp_error2547 batchN02704PlusP013Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP013Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP013Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP013DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP013Factor2654 * embedPair2542 batchN02704PlusP013Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP013Factor2654 : ℝ) * batchN02704PlusP013Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP013Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP013Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP013BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP013Factor2654)

def batchN02704PlusP014Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((52347367793712943072596661 : ℚ) /
        7378697629483820646400000000))

def batchN02704PlusP014Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP014Factor2654 : RatPair2542 := ((((((((((((((301689771223061811083372026199700
    *
    10^40
        + 6563431171396532690685112236631402006894) * 10^40
        + 4915026776051451946626488714930848171437) * 10^40
        + 1886193174684055946569390588536035141372) * 10^40
        + 7006585627442572974187776102587347935847) * 10^40
        + 6354115983375721552406919023281061603434) * 10^40
        + 3528194905637247335991479334343788730524) * 10^40
        + 3187527151477874934018933248394787884093) * 10^40
        + 5598348610667416981406363313342458702468) * 10^40
        + 88897178539823850094565214629499099749) * 10^40
        + 8104738263986453464735575962819412064884) * 10^40
        + 7914012704604537620805102195555901894399) : ℚ) /
        (((((((((((54211855738152 * 10^40
        + 9963324259336358300008021374424618391603) * 10^40
        + 6219038962453080256290789328592821191493) * 10^40
        + 590053930107729507670893252229803708421) * 10^40
        + 6225354899802779768560628121857829244083) * 10^40
        + 8621973525739187574376885969739126759429) * 10^40
        + 1850038631271090408438834887933824722951) * 10^40
        + 2727707499262468611410506846949536681408) * 10^40
        + 3493435277901733030428750567771896114350) * 10^40
        + 2774246979832632663602148225596787963057) * 10^40
        + 8016725375521483697445073175485122951020) * 10^40
        + 8629944137857102957301040574126100578304)),
    (((-((((((((87396484808449914719 * 10^40
        + 4063099590819485199982035710582130579026) * 10^40
        + 4781393422090842403507945194830909673021) * 10^40
        + 4563284421838663205697371570759171564531) * 10^40
        + 9618060451334815397870961893049936774542) * 10^40
        + 2730378864210294561471342828843665564503) * 10^40
        + 4496972308148719945827861830380330813954) * 10^40
        + 7237088814139051384101501386604109410358) * 10^40
        + 9242715025773477127266966747537585176751)) : ℚ) /
        ((((((((246758 * 10^40
        + 92297029404381644120522901562418576861) * 10^40
        + 1302986283004709531548982303256745966159) * 10^40
        + 7813148897923072823400418771400235864137) * 10^40
        + 2946699006584903967036218379096100530263) * 10^40
        + 3992188868988381057065564803111279761774) * 10^40
        + 2078701358395270609255705300662053305692) * 10^40
        + 327969446174663465997885472956591660950) * 10^40
        + 4880357661586489453609388902068829290496)))

noncomputable def batchN02704PlusP014Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP014BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP014Center2654‖ ≤ batchN02704PlusP014Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP014Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP014Input2654]
  have hs : compactExp2547 batchN02704PlusP014Input2654 14 =
      (batchN02704PlusP014Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP014Input2654 14).2 : ℝ) =
      batchN02704PlusP014Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP014Error2654]
  have h := compactExp_error2547 batchN02704PlusP014Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP014Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP014Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP014DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP014Factor2654 * embedPair2542 batchN02704PlusP014Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP014Factor2654 : ℝ) * batchN02704PlusP014Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP014Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP014Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP014BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP014Factor2654)

def batchN02704PlusP015Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((56988694746382884754536097 : ℚ) /
        7378697629483820646400000000))

def batchN02704PlusP015Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP015Factor2654 : RatPair2542 := ((((((((((((((301689771147644288292607661863811
    *
    10^40
        + 7565665125006329754218256888116335814806) * 10^40
        + 9069724862054029380966979999909569371184) * 10^40
        + 2380351276964064293289342129534311843311) * 10^40
        + 9037397560630584583421652071944244675964) * 10^40
        + 3275092344307466060754461594946533553785) * 10^40
        + 9002975148549578072769185604789818519277) * 10^40
        + 9758344464703603397941346680800081803967) * 10^40
        + 7175038265906738379018487660031358160195) * 10^40
        + 6283422122726360572036492415845893670740) * 10^40
        + 5527704624542480138978355237070935486197) * 10^40
        + 8317166887719909185969620030757673721207) : ℚ) /
        (((((((((((54211855738152 * 10^40
        + 9963324259336358300008021374424618391603) * 10^40
        + 6219038962453080256290789328592821191493) * 10^40
        + 590053930107729507670893252229803708421) * 10^40
        + 6225354899802779768560628121857829244083) * 10^40
        + 8621973525739187574376885969739126759429) * 10^40
        + 1850038631271090408438834887933824722951) * 10^40
        + 2727707499262468611410506846949536681408) * 10^40
        + 3493435277901733030428750567771896114350) * 10^40
        + 2774246979832632663602148225596787963057) * 10^40
        + 8016725375521483697445073175485122951020) * 10^40
        + 8629944137857102957301040574126100578304)),
    (((-((((((((95145406625689888530 * 10^40
        + 3384178230321203142251970686172495127123) * 10^40
        + 8877192312837921325340385390790751511539) * 10^40
        + 7662688292687810461158255415051064814692) * 10^40
        + 7559842847299249872082029447362278634671) * 10^40
        + 8042539521721784272065490479942998008066) * 10^40
        + 8572306502857792592786511031551948436184) * 10^40
        + 2818789096629836774411078555721197413509) * 10^40
        + 565796767169465736379674461412522343499)) : ℚ) /
        ((((((((246758 * 10^40
        + 92297029404381644120522901562418576861) * 10^40
        + 1302986283004709531548982303256745966159) * 10^40
        + 7813148897923072823400418771400235864137) * 10^40
        + 2946699006584903967036218379096100530263) * 10^40
        + 3992188868988381057065564803111279761774) * 10^40
        + 2078701358395270609255705300662053305692) * 10^40
        + 327969446174663465997885472956591660950) * 10^40
        + 4880357661586489453609388902068829290496)))

noncomputable def batchN02704PlusP015Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP015BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP015Center2654‖ ≤ batchN02704PlusP015Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP015Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP015Input2654]
  have hs : compactExp2547 batchN02704PlusP015Input2654 14 =
      (batchN02704PlusP015Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP015Input2654 14).2 : ℝ) =
      batchN02704PlusP015Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP015Error2654]
  have h := compactExp_error2547 batchN02704PlusP015Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP015Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP015Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP015DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP015Factor2654 * embedPair2542 batchN02704PlusP015Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP015Factor2654 : ℝ) * batchN02704PlusP015Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP015Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP015Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP015BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP015Factor2654)

def batchN02704PlusP016Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((30171440028794791767436959 : ℚ) /
        3689348814741910323200000000))

def batchN02704PlusP016Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP016Factor2654 : RatPair2542 := ((((((((((((((75422442772289009715776953517944
    *
    10^40
        + 2171555216787098009432885191689324978445) * 10^40
        + 3613576682781741803095467464191527590332) * 10^40
        + 3017840043069694650560158158700850539251) * 10^40
        + 8424285577813526704809720816189950320588) * 10^40
        + 8170392953188312177830022857768312270257) * 10^40
        + 4841953540728942166054124118220064712638) * 10^40
        + 792445403017162672097185038446469442941) * 10^40
        + 6380133942766993962899803358269947490690) * 10^40
        + 9523932427569111334472328308810755144112) * 10^40
        + 3631727131812589537162474113915458948473) * 10^40
        + 7774715932477515552161654068309312740343) : ℚ) /
        (((((((((((13552963934538 * 10^40
        + 2490831064834089575002005343606154597900) * 10^40
        + 9054759740613270064072697332148205297873) * 10^40
        + 2647513482526932376917723313057450927105) * 10^40
        + 4056338724950694942140157030464457311020) * 10^40
        + 9655493381434796893594221492434781689857) * 10^40
        + 2962509657817772602109708721983456180737) * 10^40
        + 8181926874815617152852626711737384170352) * 10^40
        + 873358819475433257607187641942974028587) * 10^40
        + 5693561744958158165900537056399196990764) * 10^40
        + 4504181343880370924361268293871280737755) * 10^40
        + 2157486034464275739325260143531525144576)),
    (((-((((((((4197724277794429056 * 10^40
        + 8332890509367212245028722468983850576127) * 10^40
        + 5045278039266984898347551738239570648210) * 10^40
        + 3361174353544557386655504464849043285327) * 10^40
        + 1887511586547612859166806110223247866104) * 10^40
        + 532868801359299273471747320497424153) * 10^40
        + 9122645615617262597083578709207712072522) * 10^40
        + 553181332123108926247561912949494111892) * 10^40
        + 2756895152625586067273275445868644371879)) : ℚ) /
        ((((((((10281 * 10^40
        + 5837179042891849235171688454231767440702) * 10^40
        + 5470957761791862897147874262635697748589) * 10^40
        + 9908881204080128034308350782141676494339) * 10^40
        + 539445791941037665293175765795670855427) * 10^40
        + 6416341202874515877377731866796303323407) * 10^40
        + 2586612556599802942052321054194252221070) * 10^40
        + 5013665393590610977749911894706524652539) * 10^40
        + 6036681569232770393900391204252867887104)))

noncomputable def batchN02704PlusP016Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP016BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP016Center2654‖ ≤ batchN02704PlusP016Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP016Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP016Input2654]
  have hs : compactExp2547 batchN02704PlusP016Input2654 14 =
      (batchN02704PlusP016Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP016Input2654 14).2 : ℝ) =
      batchN02704PlusP016Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP016Error2654]
  have h := compactExp_error2547 batchN02704PlusP016Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP016Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP016Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP016DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP016Factor2654 * embedPair2542 batchN02704PlusP016Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP016Factor2654 : ℝ) * batchN02704PlusP016Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP016Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP016Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP016BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP016Factor2654)

def batchN02704PlusP017Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((66858175325789869447510077 : ℚ) /
        7378697629483820646400000000))

def batchN02704PlusP017Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP017Factor2654 : RatPair2542 := ((((((((((((((301689770965989854441601827045520
    *
    10^40
        + 5983592021876515188275206038046679547170) * 10^40
        + 5500499923218226910744592035817690226348) * 10^40
        + 3922104620091449121871099261771782448010) * 10^40
        + 3490234637311942247487276875370199247522) * 10^40
        + 3663351922997983512254956614095799196542) * 10^40
        + 3231549759292459134836807121672768184518) * 10^40
        + 3375633577471680714680023079829467124522) * 10^40
        + 2084396377588206319736434926515594144563) * 10^40
        + 5965959837694695464937163304774449184520) * 10^40
        + 291396308409891213407326478515218061583) * 10^40
        + 3331657470495939792228934206418765036527) : ℚ) /
        (((((((((((54211855738152 * 10^40
        + 9963324259336358300008021374424618391603) * 10^40
        + 6219038962453080256290789328592821191493) * 10^40
        + 590053930107729507670893252229803708421) * 10^40
        + 6225354899802779768560628121857829244083) * 10^40
        + 8621973525739187574376885969739126759429) * 10^40
        + 1850038631271090408438834887933824722951) * 10^40
        + 2727707499262468611410506846949536681408) * 10^40
        + 3493435277901733030428750567771896114350) * 10^40
        + 2774246979832632663602148225596787963057) * 10^40
        + 8016725375521483697445073175485122951020) * 10^40
        + 8629944137857102957301040574126100578304)),
    (((-((((((((5315380286854676477 * 10^40
        + 1606751699405708826374039103753046971910) * 10^40
        + 1842187070719583928037339181299318053465) * 10^40
        + 4635582831499220847254378301593970840040) * 10^40
        + 3303542736827395842795438682398799798808) * 10^40
        + 7726983816113884174061946678861233883449) * 10^40
        + 4187927393070930272817970188785300507807) * 10^40
        + 2624205548417519804938299343179188701984) * 10^40
        + 6138201761959108307467737660541253644059)) : ℚ) /
        ((((((((11750 * 10^40
        + 3813918906162113411624786804836305646517) * 10^40
        + 1966808870619271882454713443012225998388) * 10^40
        + 5610149947520146324923829465304773136387) * 10^40
        + 4902223762218328760335058018052195263345) * 10^40
        + 8761532803285161002717407847767203798179) * 10^40
        + 7241842921828346219488366919079145395509) * 10^40
        + 1444189021246412545999899308236028174330) * 10^40
        + 9756207507694594735886161376288991870976)))

noncomputable def batchN02704PlusP017Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP017BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP017Center2654‖ ≤ batchN02704PlusP017Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP017Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP017Input2654]
  have hs : compactExp2547 batchN02704PlusP017Input2654 14 =
      (batchN02704PlusP017Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP017Input2654 14).2 : ℝ) =
      batchN02704PlusP017Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP017Error2654]
  have h := compactExp_error2547 batchN02704PlusP017Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP017Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP017Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP017DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP017Factor2654 * embedPair2542 batchN02704PlusP017Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP017Factor2654 : ℝ) * batchN02704PlusP017Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP017Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP017Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP017BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP017Factor2654)

def batchN02704PlusP018Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((17330367457162959994191563 : ℚ) /
        1844674407370955161600000000))

def batchN02704PlusP018Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP018Factor2654 : RatPair2542 := ((((((((((((((18855610682258525361527988010075
    *
    10^40
        + 9302563132778421088672626531907230050668) * 10^40
        + 4800363902310358555062189295017472899263) * 10^40
        + 7964985088091771474677514577057885466980) * 10^40
        + 7342250360453016214545039082281959010087) * 10^40
        + 4200397313093103461913621948479509406865) * 10^40
        + 6068147095080667299056981921125534237477) * 10^40
        + 3520837386210170973508556205119908190338) * 10^40
        + 5332844695797900964959614846719091304472) * 10^40
        + 986450121482335336878314301004028549287) * 10^40
        + 244576506234692480967164176961425624342) * 10^40
        + 1156290888333745877681743349641701467647) : ℚ) /
        (((((((((((3388240983634 * 10^40
        + 5622707766208522393750501335901538649475) * 10^40
        + 2263689935153317516018174333037051324468) * 10^40
        + 3161878370631733094229430828264362731776) * 10^40
        + 3514084681237673735535039257616114327755) * 10^40
        + 2413873345358699223398555373108695422464) * 10^40
        + 3240627414454443150527427180495864045184) * 10^40
        + 4545481718703904288213156677934346042588) * 10^40
        + 218339704868858314401796910485743507146) * 10^40
        + 8923390436239539541475134264099799247691) * 10^40
        + 1126045335970092731090317073467820184438) * 10^40
        + 8039371508616068934831315035882881286144)),
    (((-((((((((1808368381090752513 * 10^40
        + 5032202762178471411883089734524649342482) * 10^40
        + 8297687638689726598099088016438450741965) * 10^40
        + 7993403801563436006744183812942120496347) * 10^40
        + 9213523781705513074927355199633002697733) * 10^40
        + 7693538466910768589088381211006235721529) * 10^40
        + 2506533940317043529004428011134783248345) * 10^40
        + 1228661575938042450503638734112235446341) * 10^40
        + 3201057972369464831865402398401187054801)) : ℚ) /
        ((((((((3855 * 10^40
        + 5938942141084443463189383170336912790263) * 10^40
        + 4551609160671948586430452848488386655721) * 10^40
        + 2465830451530048012865631543303128685377) * 10^40
        + 1452292171977889124484940912173376570785) * 10^40
        + 3656127951077943454016649450048613746277) * 10^40
        + 7219979708724926103269620395322844582901) * 10^40
        + 4380124522596479116656216960514946744702) * 10^40
        + 3513755588462288897712646701594825457664)))

noncomputable def batchN02704PlusP018Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP018BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP018Center2654‖ ≤ batchN02704PlusP018Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP018Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP018Input2654]
  have hs : compactExp2547 batchN02704PlusP018Input2654 14 =
      (batchN02704PlusP018Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP018Input2654 14).2 : ℝ) =
      batchN02704PlusP018Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP018Error2654]
  have h := compactExp_error2547 batchN02704PlusP018Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP018Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP018Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP018DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP018Factor2654 * embedPair2542 batchN02704PlusP018Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP018Factor2654 : ℝ) * batchN02704PlusP018Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP018Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP018Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP018BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP018Factor2654)

def batchN02704PlusP019Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((3688665669635304979192041 : ℚ) /
        368934881474191032320000000))

def batchN02704PlusP019Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP019Factor2654 : RatPair2542 := ((((((((((((((18855610676341405265881623011946
    *
    10^40
        + 4056789694039463654838664772275039264682) * 10^40
        + 6758605787147018286909515994403256890967) * 10^40
        + 8099747314434547668213963170084894468045) * 10^40
        + 8485743425783734472972520640115156663916) * 10^40
        + 7565881642006841122113916305373739212034) * 10^40
        + 547389986493413266341799963757946096636) * 10^40
        + 7053818295619755821632704376337823375249) * 10^40
        + 4384087823782654289652742178921402141002) * 10^40
        + 4146642654252582850064650707922265347483) * 10^40
        + 5048769358307725640789005746612297737859) * 10^40
        + 9806261164086502438578733420518562542543) : ℚ) /
        (((((((((((3388240983634 * 10^40
        + 5622707766208522393750501335901538649475) * 10^40
        + 2263689935153317516018174333037051324468) * 10^40
        + 3161878370631733094229430828264362731776) * 10^40
        + 3514084681237673735535039257616114327755) * 10^40
        + 2413873345358699223398555373108695422464) * 10^40
        + 3240627414454443150527427180495864045184) * 10^40
        + 4545481718703904288213156677934346042588) * 10^40
        + 218339704868858314401796910485743507146) * 10^40
        + 8923390436239539541475134264099799247691) * 10^40
        + 1126045335970092731090317073467820184438) * 10^40
        + 8039371508616068934831315035882881286144)),
    (((-((((((((213833587571993556 * 10^40
        + 7828754270483782786649364416755053428969) * 10^40
        + 7697958132880402151433221648516947284127) * 10^40
        + 7895664164330831031212669265243751199598) * 10^40
        + 3958510208969013615005176290971221595004) * 10^40
        + 555184735654299824150308642043437078414) * 10^40
        + 6032532682853113442046439586544263177433) * 10^40
        + 4680958294420693491499258704153908384152) * 10^40
        + 2268402626456735905346735102913538727055)) : ℚ) /
        ((((((((428 * 10^40
        + 3993215793453827051465487018926323643362) * 10^40
        + 6061289906741327620714494760943154072857) * 10^40
        + 9162870050170005334762847949255903187264) * 10^40
        + 1272476907997543236053882323574819618976) * 10^40
        + 1517347550119771494890738827783179305141) * 10^40
        + 9691108856524991789252180043924760509211) * 10^40
        + 2708902724732942124072912995612771860522) * 10^40
        + 4834861732051365433079182966843869495296)))

noncomputable def batchN02704PlusP019Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP019BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP019Center2654‖ ≤ batchN02704PlusP019Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP019Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP019Input2654]
  have hs : compactExp2547 batchN02704PlusP019Input2654 14 =
      (batchN02704PlusP019Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP019Input2654 14).2 : ℝ) =
      batchN02704PlusP019Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP019Error2654]
  have h := compactExp_error2547 batchN02704PlusP019Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP019Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP019Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP019DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP019Factor2654 * embedPair2542 batchN02704PlusP019Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP019Factor2654 : ℝ) * batchN02704PlusP019Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP019Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP019Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP019BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP019Factor2654)

def batchN02704PlusP020Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((78614337331324960832264269 : ℚ) /
        7378697629483820646400000000))

def batchN02704PlusP020Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP020Factor2654 : RatPair2542 := ((((((((((((((301689770711826359955766767791645
    *
    10^40
        + 8183924206478620465876430648704720564789) * 10^40
        + 9282890949107586110509570365977174206560) * 10^40
        + 1190508781193591114832069308093251675604) * 10^40
        + 9616712246248169646839908039861470215855) * 10^40
        + 4397098022781032351915310506107452217394) * 10^40
        + 9203866570425177199376672500934909201999) * 10^40
        + 3490767851621027497745174496378451329027) * 10^40
        + 7440617248683304588081686886658059156931) * 10^40
        + 4048494203722124997988755067647130132952) * 10^40
        + 3218386562227801419653583248978492132327) * 10^40
        + 2594754239380332003678168346602788431439) : ℚ) /
        (((((((((((54211855738152 * 10^40
        + 9963324259336358300008021374424618391603) * 10^40
        + 6219038962453080256290789328592821191493) * 10^40
        + 590053930107729507670893252229803708421) * 10^40
        + 6225354899802779768560628121857829244083) * 10^40
        + 8621973525739187574376885969739126759429) * 10^40
        + 1850038631271090408438834887933824722951) * 10^40
        + 2727707499262468611410506846949536681408) * 10^40
        + 3493435277901733030428750567771896114350) * 10^40
        + 2774246979832632663602148225596787963057) * 10^40
        + 8016725375521483697445073175485122951020) * 10^40
        + 8629944137857102957301040574126100578304)),
    (((-((((((((18750067445294895468 * 10^40
        + 7315203293526473730848939749049316970859) * 10^40
        + 2508727925633526546051404331984558452938) * 10^40
        + 7723383049407014056790479053552828992621) * 10^40
        + 5469258381784346400052645436850586912307) * 10^40
        + 1816691430071146797260262336878362516757) * 10^40
        + 4590700100061770522910246067656660327963) * 10^40
        + 764248002475179378387706493452392551471) * 10^40
        + 1495691009079251025451285112728080078657)) : ℚ) /
        ((((((((35251 * 10^40
        + 1441756718486340234874360414508916939551) * 10^40
        + 5900426611857815647364140329036677995165) * 10^40
        + 6830449842560438974771488395914319409162) * 10^40
        + 4706671286654986281005174054156585790037) * 10^40
        + 6284598409855483008152223543301611394539) * 10^40
        + 1725528765485038658465100757237436186527) * 10^40
        + 4332567063739237637999697924708084522992) * 10^40
        + 9268622523083784207658484128866975612928)))

noncomputable def batchN02704PlusP020Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP020BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP020Center2654‖ ≤ batchN02704PlusP020Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP020Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP020Input2654]
  have hs : compactExp2547 batchN02704PlusP020Input2654 14 =
      (batchN02704PlusP020Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP020Input2654 14).2 : ℝ) =
      batchN02704PlusP020Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP020Error2654]
  have h := compactExp_error2547 batchN02704PlusP020Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP020Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP020Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP020DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP020Factor2654 * embedPair2542 batchN02704PlusP020Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP020Factor2654 : ℝ) * batchN02704PlusP020Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP020Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP020Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP020BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP020Factor2654)

def batchN02704PlusP021Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((82654361045867903481379437 : ℚ) /
        7378697629483820646400000000))

def batchN02704PlusP021Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP021Factor2654 : RatPair2542 := ((((((((((((((301689770614998425925155267831197
    *
    10^40
        + 5766250474967043290282611056218749280622) * 10^40
        + 5822589312855536261988879787570693946195) * 10^40
        + 230650474218538654190014025261731803735) * 10^40
        + 1719432344602449563645586259380826517528) * 10^40
        + 7087378441579854628323210646526355389109) * 10^40
        + 783749996114008130963031318498899723285) * 10^40
        + 5200840304185043419910299057160672852642) * 10^40
        + 9833209063048957051820141256817632931461) * 10^40
        + 7810188552438663179550164296165286584798) * 10^40
        + 3568891727285261943064303939252751755153) * 10^40
        + 449631151948324611561831416419446993167) : ℚ) /
        (((((((((((54211855738152 * 10^40
        + 9963324259336358300008021374424618391603) * 10^40
        + 6219038962453080256290789328592821191493) * 10^40
        + 590053930107729507670893252229803708421) * 10^40
        + 6225354899802779768560628121857829244083) * 10^40
        + 8621973525739187574376885969739126759429) * 10^40
        + 1850038631271090408438834887933824722951) * 10^40
        + 2727707499262468611410506846949536681408) * 10^40
        + 3493435277901733030428750567771896114350) * 10^40
        + 2774246979832632663602148225596787963057) * 10^40
        + 8016725375521483697445073175485122951020) * 10^40
        + 8629944137857102957301040574126100578304)),
    (((-((((((((45998496278087289253 * 10^40
        + 4136595136685308252915274115328134741739) * 10^40
        + 1577382730237781739922154609013770991979) * 10^40
        + 6326302438824607360229172391140992571031) * 10^40
        + 1906877393860534698430318342049147048506) * 10^40
        + 7484986884096504316460177841155737601113) * 10^40
        + 142984622796872712797368710955796601535) * 10^40
        + 6846777638305996347836194637521525757736) * 10^40
        + 1939002124778604471609830348568729546573)) : ℚ) /
        ((((((((82252 * 10^40
        + 6697432343134793881373507633854139525620) * 10^40
        + 3767662094334903177182994101085581988719) * 10^40
        + 9271049632641024274466806257133411954712) * 10^40
        + 4315566335528301322345406126365366843421) * 10^40
        + 1330729622996127019021854934370426587258) * 10^40
        + 692900452798423536418568433554017768564) * 10^40
        + 109323148724887821999295157652197220316) * 10^40
        + 8293452553862163151203129634022943096832)))

noncomputable def batchN02704PlusP021Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP021BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP021Center2654‖ ≤ batchN02704PlusP021Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP021Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP021Input2654]
  have hs : compactExp2547 batchN02704PlusP021Input2654 14 =
      (batchN02704PlusP021Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP021Input2654 14).2 : ℝ) =
      batchN02704PlusP021Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP021Error2654]
  have h := compactExp_error2547 batchN02704PlusP021Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP021Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP021Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP021DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP021Factor2654 * embedPair2542 batchN02704PlusP021Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP021Factor2654 : ℝ) * batchN02704PlusP021Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP021Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP021Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP021BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP021Factor2654)

def batchN02704PlusP022Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((16944438833431689477671183 : ℚ) /
        1475739525896764129280000000))

def batchN02704PlusP022Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP022Factor2654 : RatPair2542 := ((((((((((((((301689770563561289454095720500509
    *
    10^40
        + 9023854770256177288947494591891593581683) * 10^40
        + 6351019841636296669156545685542209752317) * 10^40
        + 9150409622479718091081003555106736792606) * 10^40
        + 9790747880866134295939087399215929218977) * 10^40
        + 3373063006946414904304621381259229528240) * 10^40
        + 3550379862287977659426026742100538884440) * 10^40
        + 7911749855694929180160569206136900680874) * 10^40
        + 5199575820107936789195746365128940851912) * 10^40
        + 3171071605030012756549736446433248389363) * 10^40
        + 9544017430774279666411472822453141357565) * 10^40
        + 2207687173451143727483918951265589227263) : ℚ) /
        (((((((((((54211855738152 * 10^40
        + 9963324259336358300008021374424618391603) * 10^40
        + 6219038962453080256290789328592821191493) * 10^40
        + 590053930107729507670893252229803708421) * 10^40
        + 6225354899802779768560628121857829244083) * 10^40
        + 8621973525739187574376885969739126759429) * 10^40
        + 1850038631271090408438834887933824722951) * 10^40
        + 2727707499262468611410506846949536681408) * 10^40
        + 3493435277901733030428750567771896114350) * 10^40
        + 2774246979832632663602148225596787963057) * 10^40
        + 8016725375521483697445073175485122951020) * 10^40
        + 8629944137857102957301040574126100578304)),
    (((-((((((((141447837126210203382 * 10^40
        + 7589040448029385198874458418875041197553) * 10^40
        + 7028429656119172111325509658213097890587) * 10^40
        + 6976936193283834513967064663968916254629) * 10^40
        + 4065526555814044136020097172583183778293) * 10^40
        + 1580127837123869424980093343888517439872) * 10^40
        + 4687594288133878233541848393510868819298) * 10^40
        + 6510131687529281099138666725296957866453) * 10^40
        + 2617194112890653846705831407876468981585)) : ℚ) /
        ((((((((246758 * 10^40
        + 92297029404381644120522901562418576861) * 10^40
        + 1302986283004709531548982303256745966159) * 10^40
        + 7813148897923072823400418771400235864137) * 10^40
        + 2946699006584903967036218379096100530263) * 10^40
        + 3992188868988381057065564803111279761774) * 10^40
        + 2078701358395270609255705300662053305692) * 10^40
        + 327969446174663465997885472956591660950) * 10^40
        + 4880357661586489453609388902068829290496)))

noncomputable def batchN02704PlusP022Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP022BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP022Center2654‖ ≤ batchN02704PlusP022Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP022Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP022Input2654]
  have hs : compactExp2547 batchN02704PlusP022Input2654 14 =
      (batchN02704PlusP022Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP022Input2654 14).2 : ℝ) =
      batchN02704PlusP022Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP022Error2654]
  have h := compactExp_error2547 batchN02704PlusP022Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP022Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP022Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP022DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP022Factor2654 * embedPair2542 batchN02704PlusP022Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP022Factor2654 : ℝ) * batchN02704PlusP022Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP022Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP022Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP022BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP022Factor2654)

def batchN02704PlusP023Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((45342070652492160469014283 : ℚ) /
        3689348814741910323200000000))

def batchN02704PlusP023Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP023Factor2654 : RatPair2542 := ((((((((((((((75422442602035934095034238733116
    *
    10^40
        + 1235504256158246128115130175741553656754) * 10^40
        + 748113772060107308428032423576394310112) * 10^40
        + 9534892317519961958475562307695964874107) * 10^40
        + 1724342743230764363996624123826092226822) * 10^40
        + 7374773228327480108887311426026988720318) * 10^40
        + 3150628814225913532036672111329201330391) * 10^40
        + 1618469616217604289003966899788063230748) * 10^40
        + 1712417599416048616999220896637599332925) * 10^40
        + 1946384086249692547243771657534841573812) * 10^40
        + 4237949442378618399441759501814040687502) * 10^40
        + 583607356710057591377836434273267487871) : ℚ) /
        (((((((((((13552963934538 * 10^40
        + 2490831064834089575002005343606154597900) * 10^40
        + 9054759740613270064072697332148205297873) * 10^40
        + 2647513482526932376917723313057450927105) * 10^40
        + 4056338724950694942140157030464457311020) * 10^40
        + 9655493381434796893594221492434781689857) * 10^40
        + 2962509657817772602109708721983456180737) * 10^40
        + 8181926874815617152852626711737384170352) * 10^40
        + 873358819475433257607187641942974028587) * 10^40
        + 5693561744958158165900537056399196990764) * 10^40
        + 4504181343880370924361268293871280737755) * 10^40
        + 2157486034464275739325260143531525144576)),
    (((-((((((((18925199846683183693 * 10^40
        + 3740989965309464647316090743877942987415) * 10^40
        + 7679835408377837344222145007628129596370) * 10^40
        + 2454785914847943795481315489718082383662) * 10^40
        + 8311992954352432191435021089771614018077) * 10^40
        + 7486785702366087552656375982345869406848) * 10^40
        + 3329436923255940898651367621358015264938) * 10^40
        + 3844951385040402375832719861798311008121) * 10^40
        + 3880893960737496778844431857443933326097)) : ℚ) /
        ((((((((30844 * 10^40
        + 7511537128675547705515065362695302322107) * 10^40
        + 6412873285375588691443622787907093245769) * 10^40
        + 9726643612240384102925052346425029483017) * 10^40
        + 1618337375823112995879527297387012566282) * 10^40
        + 9249023608623547632133195600388909970221) * 10^40
        + 7759837669799408826156963162582756663211) * 10^40
        + 5040996180771832933249735684119573957618) * 10^40
        + 8110044707698311181701173612758603661312)))

noncomputable def batchN02704PlusP023Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP023BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP023Center2654‖ ≤ batchN02704PlusP023Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP023Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP023Input2654]
  have hs : compactExp2547 batchN02704PlusP023Input2654 14 =
      (batchN02704PlusP023Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP023Input2654 14).2 : ℝ) =
      batchN02704PlusP023Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP023Error2654]
  have h := compactExp_error2547 batchN02704PlusP023Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP023Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP023Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP023DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP023Factor2654 * embedPair2542 batchN02704PlusP023Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP023Factor2654 : ℝ) * batchN02704PlusP023Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP023Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP023Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP023BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP023Factor2654)

def batchN02704PlusP024Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((46712005387750232020650197 : ℚ) /
        3689348814741910323200000000))

def batchN02704PlusP024Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP024Factor2654 : RatPair2542 := ((((((((((((((75422442583294208653955520658803
    *
    10^40
        + 6448784906031634792519929765609687246541) * 10^40
        + 7279106296344878899841904850119378487974) * 10^40
        + 3361977263914528919254689176165521044192) * 10^40
        + 9199180138617535220660128492822673547699) * 10^40
        + 5068724408978509707451185740667608425679) * 10^40
        + 3073965273850283785599414091092836486426) * 10^40
        + 2726908513747668934996384195146352305998) * 10^40
        + 2378554175204381307434430181878505250623) * 10^40
        + 8289014215873189734730340829407046175960) * 10^40
        + 967595017196084345207242133591798729517) * 10^40
        + 9150016138882710007026152159184804243391) : ℚ) /
        (((((((((((13552963934538 * 10^40
        + 2490831064834089575002005343606154597900) * 10^40
        + 9054759740613270064072697332148205297873) * 10^40
        + 2647513482526932376917723313057450927105) * 10^40
        + 4056338724950694942140157030464457311020) * 10^40
        + 9655493381434796893594221492434781689857) * 10^40
        + 2962509657817772602109708721983456180737) * 10^40
        + 8181926874815617152852626711737384170352) * 10^40
        + 873358819475433257607187641942974028587) * 10^40
        + 5693561744958158165900537056399196990764) * 10^40
        + 4504181343880370924361268293871280737755) * 10^40
        + 2157486034464275739325260143531525144576)),
    (((-((((((((19496993067508435062 * 10^40
        + 2616027046236304133103832084992327504144) * 10^40
        + 1193798325522255693800543935426082398457) * 10^40
        + 649429044131039712821448444428093281765) * 10^40
        + 5433773229236587387673035314384018580671) * 10^40
        + 7685883877951457977469438144682130456340) * 10^40
        + 2759326606689861435645496602762722578788) * 10^40
        + 5320496019846081962439194604457340766822) * 10^40
        + 4523984343655486711130050128782878013903)) : ℚ) /
        ((((((((30844 * 10^40
        + 7511537128675547705515065362695302322107) * 10^40
        + 6412873285375588691443622787907093245769) * 10^40
        + 9726643612240384102925052346425029483017) * 10^40
        + 1618337375823112995879527297387012566282) * 10^40
        + 9249023608623547632133195600388909970221) * 10^40
        + 7759837669799408826156963162582756663211) * 10^40
        + 5040996180771832933249735684119573957618) * 10^40
        + 8110044707698311181701173612758603661312)))

noncomputable def batchN02704PlusP024Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP024BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP024Center2654‖ ≤ batchN02704PlusP024Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP024Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP024Input2654]
  have hs : compactExp2547 batchN02704PlusP024Input2654 14 =
      (batchN02704PlusP024Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP024Input2654 14).2 : ℝ) =
      batchN02704PlusP024Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP024Error2654]
  have h := compactExp_error2547 batchN02704PlusP024Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP024Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP024Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP024DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP024Factor2654 * embedPair2542 batchN02704PlusP024Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP024Factor2654 : ℝ) * batchN02704PlusP024Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP024Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP024Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP024BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP024Factor2654)

def batchN02704PlusP025Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((1513426630246391746815783 : ℚ) /
        115292150460684697600000000))

def batchN02704PlusP025Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP025Factor2654 : RatPair2542 := ((((((((((((((73654729061530620790361731729 *
    10^40
        + 5666745161974882525360683528944082137816) * 10^40
        + 6906741109306234400283320958842218451369) * 10^40
        + 6636327695773531527701226529220565971345) * 10^40
        + 5612013992416370834030982212441600724204) * 10^40
        + 7351577232428899111068253290011877210044) * 10^40
        + 3344262263254933258485109427073937376317) * 10^40
        + 6564423090805141519838559537053947340925) * 10^40
        + 290179816907122986513212231559994968824) * 10^40
        + 3210349388039824966386660998927316158864) * 10^40
        + 8216026380161990333394975515188453424925) * 10^40
        + 6793563687630693378572627264458518041927) : ℚ) /
        (((((((((((13235316342 * 10^40
        + 3225088702211752040600587895843365385349) * 10^40
        + 5126030038809192646546945993488425981736) * 10^40
        + 2043601087385280207399333714172907666921) * 10^40
        + 13726893286084663029433747100062946592) * 10^40
        + 7939116692755307418841400606926205841494) * 10^40
        + 12658700837712668556747762423811968926) * 10^40
        + 5017755787963687126125832643273181039228) * 10^40
        + 8594602889472143977790632019181584935574) * 10^40
        + 7925481993891560701333887243219139840811) * 10^40
        + 2934086114593633174730821551068233672595) * 10^40
        + 4640778794955531519276684824358917505024)),
    (((-((((((((4196461132739 * 10^40
        + 1159180886422384288799361897294282471951) * 10^40
        + 4514581937131618606169804969585197063764) * 10^40
        + 8920620600397939034991517025392735372564) * 10^40
        + 3784690803474763957824364046982651037707) * 10^40
        + 2364999944466583599589477907882649050792) * 10^40
        + 6014919231751271252838932502117521706596) * 10^40
        + 9870078353161268742646841782567699426166) * 10^40
        + 3820638120598027965174972546516853843183)) : ℚ) /
        (((((((64034496808137164586427756602044697519 * 10^40
        + 3822136997118743144047264346920254850238) * 10^40
        + 2542139113371684221619919326689292528846) * 10^40
        + 2700911877345364280879843758205968612777) * 10^40
        + 3085162986500769089377813457711273066495) * 10^40
        + 5129240440283051533478992728297053243988) * 10^40
        + 7976015060527813092047852652358631807615) * 10^40
        + 1026758333591737853238098082494123343872)))

noncomputable def batchN02704PlusP025Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP025BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP025Center2654‖ ≤ batchN02704PlusP025Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP025Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP025Input2654]
  have hs : compactExp2547 batchN02704PlusP025Input2654 14 =
      (batchN02704PlusP025Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP025Input2654 14).2 : ℝ) =
      batchN02704PlusP025Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP025Error2654]
  have h := compactExp_error2547 batchN02704PlusP025Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP025Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP025Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP025DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP025Factor2654 * embedPair2542 batchN02704PlusP025Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP025Factor2654 : ℝ) * batchN02704PlusP025Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP025Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP025Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP025BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP025Factor2654)

def batchN02704PlusP026Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((3136563586529957941722987 : ℚ) /
        230584300921369395200000000))

def batchN02704PlusP026Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP026Factor2654 : RatPair2542 := ((((((((((((((294618916145629504907976214979 *
    10^40
        + 6702147120172990798877100789355482016415) * 10^40
        + 9278100369376482531561700587229048182524) * 10^40
        + 233031990727325992810072278299798008680) * 10^40
        + 1650654150803187985548993894327367966039) * 10^40
        + 1957389850361774393154154803457447068497) * 10^40
        + 4426995920134206298169139937222314660324) * 10^40
        + 6684003140829740090800437571652465861859) * 10^40
        + 7067504008430170189575193700459607048700) * 10^40
        + 4006644140315896721493615608573845086434) * 10^40
        + 3420540435445203429288592070462311586071) * 10^40
        + 8298042171620859637046332369944062166591) : ℚ) /
        (((((((((((52941265369 * 10^40
        + 2900354808847008162402351583373461541398) * 10^40
        + 504120155236770586187783973953703926944) * 10^40
        + 8174404349541120829597334856691630667684) * 10^40
        + 54907573144338652117734988400251786371) * 10^40
        + 1756466771021229675365602427704823365976) * 10^40
        + 50634803350850674226991049695247875706) * 10^40
        + 71023151854748504503330573092724156915) * 10^40
        + 4378411557888575911162528076726339742299) * 10^40
        + 1701927975566242805335548972876559363245) * 10^40
        + 1736344458374532698923286204272934690381) * 10^40
        + 8563115179822126077106739297435670020096)),
    (((-((((((((1704637354639955 * 10^40
        + 7706900787349790267343792540211461349382) * 10^40
        + 8845356347978664313559985100383350302957) * 10^40
        + 1618157925900884362207252780434417829730) * 10^40
        + 3663830811346251464414647510662158208402) * 10^40
        + 1366927361752496354199234402810762231025) * 10^40
        + 2343296354916331733933879048147113434154) * 10^40
        + 2380801972122149922606575073159191846764) * 10^40
        + 173661056682884795108589984547269220731)) : ℚ) /
        ((((((((2 * 10^40
        + 5101522748789768517879680588001521427597) * 10^40
        + 8277702870547312466527623992739901293395) * 10^40
        + 6518532441700214875008376062202671307737) * 10^40
        + 8757455919382798104898753216739696208704) * 10^40
        + 9383890708301483036102875422819042066241) * 10^40
        + 662252590956201123765149492444871643608) * 10^40
        + 6597903726902732082758239724583668585120) * 10^40
        + 2489266767961238469334448337696350797824)))

noncomputable def batchN02704PlusP026Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP026BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP026Center2654‖ ≤ batchN02704PlusP026Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP026Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP026Input2654]
  have hs : compactExp2547 batchN02704PlusP026Input2654 14 =
      (batchN02704PlusP026Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP026Input2654 14).2 : ℝ) =
      batchN02704PlusP026Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP026Error2654]
  have h := compactExp_error2547 batchN02704PlusP026Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP026Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP026Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP026DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP026Factor2654 * embedPair2542 batchN02704PlusP026Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP026Factor2654 : ℝ) * batchN02704PlusP026Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP026Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP026Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP026BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP026Factor2654)

def batchN02704PlusP027Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((6589758326498808710472677 : ℚ) /
        461168601842738790400000000))

def batchN02704PlusP027Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP027Factor2654 : RatPair2542 := ((((((((((((((1178475663977234684036292255432 *
    10^40
        + 5698754796719309715406186335868050328651) * 10^40
        + 4869022185708522880725741244493602197611) * 10^40
        + 6396076891570620066421017157292372345143) * 10^40
        + 3806158217172110943479529556514704661939) * 10^40
        + 8736281349782519965035288220975606432121) * 10^40
        + 5203619066933525654887504279333807203379) * 10^40
        + 509648196421786486148306136164932403921) * 10^40
        + 1919022250425045910505413996191549677340) * 10^40
        + 3160426203980176477330592901478818104725) * 10^40
        + 4209861133419746932436617715513880606478) * 10^40
        + 2785143681519986987601663919835920230687) : ℚ) /
        (((((((((((211765061477 * 10^40
        + 1601419235388032649609406333493846165592) * 10^40
        + 2016480620947082344751135895814815707779) * 10^40
        + 2697617398164483318389339426766522670736) * 10^40
        + 219630292577354608470939953601007145484) * 10^40
        + 7025867084084918701462409710819293463904) * 10^40
        + 202539213403402696907964198780991502824) * 10^40
        + 284092607418994018013322292370896627661) * 10^40
        + 7513646231554303644650112306905358969196) * 10^40
        + 6807711902264971221342195891506237452980) * 10^40
        + 6945377833498130795693144817091738761527) * 10^40
        + 4252460719288504308426957189742680080384)),
    (((-((((((((42976261979191931 * 10^40
        + 7178835310305334595866732833888430882679) * 10^40
        + 3569851130465856381043101861457180995005) * 10^40
        + 6381709489317625701553906720276369870607) * 10^40
        + 4634424204942427126940167360439723711926) * 10^40
        + 7630344644724450739310650395340502612626) * 10^40
        + 7423493664707377838170276153672025326847) * 10^40
        + 1828964963887479796507008721224349007081) * 10^40
        + 4187925647395829624505887333746845467999)) : ℚ) /
        ((((((((60 * 10^40
        + 2436545970954444429112334112036514262347) * 10^40
        + 8664868893135499196662975825757631041495) * 10^40
        + 6444778600805157000201025492864111385709) * 10^40
        + 178942065187154517570077201752709008918) * 10^40
        + 5213376999235592866469010147657009589785) * 10^40
        + 5894062182948826970363587818676919446607) * 10^40
        + 8349689445665569986197753390008046042885) * 10^40
        + 9742402431069723264026760104712419147776)))

noncomputable def batchN02704PlusP027Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP027BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP027Center2654‖ ≤ batchN02704PlusP027Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP027Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP027Input2654]
  have hs : compactExp2547 batchN02704PlusP027Input2654 14 =
      (batchN02704PlusP027Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP027Input2654 14).2 : ℝ) =
      batchN02704PlusP027Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP027Error2654]
  have h := compactExp_error2547 batchN02704PlusP027Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP027Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP027Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP027DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP027Factor2654 * embedPair2542 batchN02704PlusP027Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP027Factor2654 : ℝ) * batchN02704PlusP027Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP027Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP027Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP027BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP027Factor2654)

def batchN02704PlusP028Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((26860467825486442936697777 : ℚ) /
        1844674407370955161600000000))

def batchN02704PlusP028Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP028Factor2654 : RatPair2542 := ((((((((((((((18855610619669764185885252893624
    *
    10^40
        + 8690498697397017576793230464693313548815) * 10^40
        + 922710142846403810166193967678399535495) * 10^40
        + 4653973844156541582461686167351552563380) * 10^40
        + 8922889918210830589352012527784470632071) * 10^40
        + 3439606361448648155179639919833750053144) * 10^40
        + 7073795388633269080801887997604362048517) * 10^40
        + 4289439288954289618260130939364683991996) * 10^40
        + 2729676249424340480593526961862735986191) * 10^40
        + 4993814706124425946242377525720953791723) * 10^40
        + 3246623858311339413322146500237238736561) * 10^40
        + 1924891675015223974961804200981400382807) : ℚ) /
        (((((((((((3388240983634 * 10^40
        + 5622707766208522393750501335901538649475) * 10^40
        + 2263689935153317516018174333037051324468) * 10^40
        + 3161878370631733094229430828264362731776) * 10^40
        + 3514084681237673735535039257616114327755) * 10^40
        + 2413873345358699223398555373108695422464) * 10^40
        + 3240627414454443150527427180495864045184) * 10^40
        + 4545481718703904288213156677934346042588) * 10^40
        + 218339704868858314401796910485743507146) * 10^40
        + 8923390436239539541475134264099799247691) * 10^40
        + 1126045335970092731090317073467820184438) * 10^40
        + 8039371508616068934831315035882881286144)),
    (((-((((((((2802803853932815298 * 10^40
        + 8091713360212333477533474530525384180249) * 10^40
        + 1710618967118090278950078823588822692273) * 10^40
        + 1560251539451601712093690573305105708695) * 10^40
        + 6393389144972195695926554168980100868257) * 10^40
        + 3928791458826155471315916291147881280627) * 10^40
        + 5401903127698879503920600002227084424593) * 10^40
        + 5169529197876726081574451263677580812429) * 10^40
        + 8208469802567571341609166782967428259419)) : ℚ) /
        ((((((((3855 * 10^40
        + 5938942141084443463189383170336912790263) * 10^40
        + 4551609160671948586430452848488386655721) * 10^40
        + 2465830451530048012865631543303128685377) * 10^40
        + 1452292171977889124484940912173376570785) * 10^40
        + 3656127951077943454016649450048613746277) * 10^40
        + 7219979708724926103269620395322844582901) * 10^40
        + 4380124522596479116656216960514946744702) * 10^40
        + 3513755588462288897712646701594825457664)))

noncomputable def batchN02704PlusP028Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP028BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP028Center2654‖ ≤ batchN02704PlusP028Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP028Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP028Input2654]
  have hs : compactExp2547 batchN02704PlusP028Input2654 14 =
      (batchN02704PlusP028Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP028Input2654 14).2 : ℝ) =
      batchN02704PlusP028Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP028Error2654]
  have h := compactExp_error2547 batchN02704PlusP028Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP028Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP028Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP028DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP028Factor2654 * embedPair2542 batchN02704PlusP028Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP028Factor2654 : ℝ) * batchN02704PlusP028Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP028Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP028Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP028BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP028Factor2654)

def batchN02704PlusP029Input2654 : RatPair2542 := ((((-((24095 * 10^40
        + 9336701194369956013507431828476244291926) * 10^40
        + 5476769362532126008868385279313067905677)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((27623869687037674802636509 : ℚ) /
        1844674407370955161600000000))

def batchN02704PlusP029Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704PlusP029Factor2654 : RatPair2542 := ((((((((((((((18855610613488297119518642639111
    *
    10^40
        + 9444102552659625472663663974672937599297) * 10^40
        + 8997195491309224240545704940717594942686) * 10^40
        + 4526118310116799640798693195854461391346) * 10^40
        + 1362560380939248261444284669084987813385) * 10^40
        + 910335785963992834492878598762936331339) * 10^40
        + 9712537007943587776273878273544312333547) * 10^40
        + 3435783680370441677325126714889117539476) * 10^40
        + 1067674079092944398186745406219102377665) * 10^40
        + 7887234972870244428308016829883475509402) * 10^40
        + 8106843599734145854850360090722982959082) * 10^40
        + 3465809526276430581780410291529134763439) : ℚ) /
        (((((((((((3388240983634 * 10^40
        + 5622707766208522393750501335901538649475) * 10^40
        + 2263689935153317516018174333037051324468) * 10^40
        + 3161878370631733094229430828264362731776) * 10^40
        + 3514084681237673735535039257616114327755) * 10^40
        + 2413873345358699223398555373108695422464) * 10^40
        + 3240627414454443150527427180495864045184) * 10^40
        + 4545481718703904288213156677934346042588) * 10^40
        + 218339704868858314401796910485743507146) * 10^40
        + 8923390436239539541475134264099799247691) * 10^40
        + 1126045335970092731090317073467820184438) * 10^40
        + 8039371508616068934831315035882881286144)),
    (((-((((((((2882462394906032117 * 10^40
        + 9368328133036951819059182904750854162373) * 10^40
        + 5720211180852256237306542958664961455033) * 10^40
        + 5057095611690516403057472522293499682764) * 10^40
        + 6823707605246578502804408270967411836619) * 10^40
        + 8670430203539320277589697803090421651062) * 10^40
        + 4767782830610291058751787264766949992400) * 10^40
        + 8157620689319154870103727910463197513930) * 10^40
        + 9808823873603738984775698704937198879959)) : ℚ) /
        ((((((((3855 * 10^40
        + 5938942141084443463189383170336912790263) * 10^40
        + 4551609160671948586430452848488386655721) * 10^40
        + 2465830451530048012865631543303128685377) * 10^40
        + 1452292171977889124484940912173376570785) * 10^40
        + 3656127951077943454016649450048613746277) * 10^40
        + 7219979708724926103269620395322844582901) * 10^40
        + 4380124522596479116656216960514946744702) * 10^40
        + 3513755588462288897712646701594825457664)))

noncomputable def batchN02704PlusP029Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704PlusP029BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP029Center2654‖ ≤ batchN02704PlusP029Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704PlusP029Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704PlusP029Input2654]
  have hs : compactExp2547 batchN02704PlusP029Input2654 14 =
      (batchN02704PlusP029Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704PlusP029Input2654 14).2 : ℝ) =
      batchN02704PlusP029Error2654 := by
    rw [hs]
    norm_num [batchN02704PlusP029Error2654]
  have h := compactExp_error2547 batchN02704PlusP029Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      batchN02704PlusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704PlusP029Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704PlusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704PlusP029Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704PlusP029DerivativeError2654 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02704PlusPosition2654 -
      embedPair2542 batchN02704PlusP029Factor2654 * embedPair2542 batchN02704PlusP029Center2654‖ ≤
        (pairMagnitude2542 batchN02704PlusP029Factor2654 : ℝ) * batchN02704PlusP029Error2654 := by
  have hx : |batchN02704PlusPosition2654| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchN02704PlusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchN02704PlusPosition2654 = embedPair2542
          batchN02704PlusP029Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704PlusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704PlusP029Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704PlusP029BaseError2654
    (embedPair_magnitude2542 batchN02704PlusP029Factor2654)

theorem batchN02704PlusGrid2654 :
    -stripRadius2303 + (2704 : ℝ) * (2 * stripRadius2303 / 10240) =
      batchN02704PlusPosition2654 := by
  norm_num [stripRadius2303, batchN02704PlusPosition2654]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchN02704PlusP000DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP001DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP002DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP003DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP004DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP005DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP006DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP007DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP008DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP009DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP010DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP011DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP012DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP013DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP014DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP015DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP016DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP017DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP018DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP019DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP020DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP021DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP022DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP023DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP024DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP025DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP026DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP027DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP028DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusP029DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704PlusGrid2654
