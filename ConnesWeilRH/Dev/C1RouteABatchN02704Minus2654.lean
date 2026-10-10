import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchN02704MinusPosition2654 : ℝ := (((-9895936151) : ℝ) /
        3200000000)

theorem batchN02704MinusZero2654 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchN02704MinusP000Center2654 : RatPair2542 := (0, 0)

def batchN02704MinusP000Factor2654 : RatPair2542 := (0, 0)

noncomputable def batchN02704MinusP000Error2654 : ℝ := 0

theorem batchN02704MinusP000Exterior2654 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02704MinusPosition2654 = 0
        := by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |batchN02704MinusPosition2654| := by
    norm_num [storedWidth, batchN02704MinusPosition2654]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem batchN02704MinusP000BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP000Center2654‖ ≤ batchN02704MinusP000Error2654 := by
  rw [batchN02704MinusP000Exterior2654]
  norm_num [batchN02704MinusP000Center2654, batchN02704MinusP000Error2654,
      batchN02704MinusZero2654]

theorem batchN02704MinusP000DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP000Factor2654 * embedPair2542 batchN02704MinusP000Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP000Factor2654 : ℝ) * batchN02704MinusP000Error2654 :=
            by
  rw [batchN02704MinusP000Exterior2654]
  norm_num [batchN02704MinusP000Factor2654, batchN02704MinusP000Center2654,
      batchN02704MinusP000Error2654,
      batchN02704MinusZero2654, pairMagnitude2542]

def batchN02704MinusP001Input2654 : RatPair2542 := ((((-((20 * 10^40
        + 8991036429139976524574151519976207695507) * 10^40
        + 4753568805857603624994734849814902306889)) : ℚ) /
        ((59 * 10^40
        + 5965149429887586107108459481843895661464) * 10^40
        + 568333469734220561590691302604800000000)),
    ((54668031270047913913566379 : ℚ) /
        230584300921369395200000000))

def batchN02704MinusP001Center2654 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN02704MinusP001Factor2654 : RatPair2542 := ((((((((((((((2794293149053 * 10^40
        + 900348551994899325417443532308639529934) * 10^40
        + 9710522538529088654650070471500910769929) * 10^40
        + 4479990442270458289031967830741372707198) * 10^40
        + 248698428736988056541191476484393601811) * 10^40
        + 7731405907555768279472498723122040572559) * 10^40
        + 7350138914669864273952564339865337840678) * 10^40
        + 6583335711105324478324462915330175460725) * 10^40
        + 3290868524264936897391797977533929774019) * 10^40
        + 4266831771218015675275192280362027662256) * 10^40
        + 325667184490966034842135547673878964867) * 10^40
        + 5504537088373545549643666245791833481147) : ℚ) /
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
    (((-((((((((12312151 * 10^40
        + 5475654836523804144501676767852827425784) * 10^40
        + 5864378771453736099203421434636979096004) * 10^40
        + 650144236762726835589793498188370268770) * 10^40
        + 5781953645459057370149168076476215408) * 10^40
        + 5783362229710023753451726523974977156797) * 10^40
        + 1251212083479524676739987297097108989573) * 10^40
        + 8635968401994411997638094311110726419458) * 10^40
        + 7389153242884109005925624072684670978283)) : ℚ) /
        (((((((3050093163439907082370504546418905483763 * 10^40
        + 12627471688809529625630990196760447195) * 10^40
        + 4408035631287601163648154772370580682660) * 10^40
        + 9763374694818108913849149985740546032921) * 10^40
        + 895785634565358934712351272341632371431) * 10^40
        + 7266286930266086384385654927261912752636) * 10^40
        + 4652652587857820583710152832941835075799) * 10^40
        + 9338010115055769106750420158131503890432)))

noncomputable def batchN02704MinusP001Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP001BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP001Center2654‖ ≤ batchN02704MinusP001Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP001Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP001Input2654]
  have hs : compactExp2547 batchN02704MinusP001Input2654 9 =
      (batchN02704MinusP001Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP001Input2654 9).2 : ℝ) =
      batchN02704MinusP001Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP001Error2654]
  have h := compactExp_error2547 batchN02704MinusP001Input2654 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          batchN02704MinusP001Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP001Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP001DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP001Factor2654 * embedPair2542 batchN02704MinusP001Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP001Factor2654 : ℝ) * batchN02704MinusP001Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP001Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP001Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP001BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP001Factor2654)

def batchN02704MinusP002Input2654 : RatPair2542 := ((((-((536 * 10^40
        + 8661499926090410127664480832514854352328) * 10^40
        + 1664516618783932279964932674095321675849)) : ℚ) /
        ((2298 * 10^40
        + 4999305507355519060301944907893290580952) * 10^40
        + 3852905515627880742725530420838400000000)),
    (((-54668031270047913913566379) : ℚ) /
        115292150460684697600000000))

def batchN02704MinusP002Center2654 : RatPair2542 := ((((-1659707957179232547945) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-14245775921432001046225) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN02704MinusP002Factor2654 : RatPair2542 := ((((-(((((((((((389486873120231830826 * 10^40
        + 3529602715412394476638703467575984120337) * 10^40
        + 6636351919434848200912266295608310861777) * 10^40
        + 2238582928148208090242927665169095195457) * 10^40
        + 8071691741305989942947501166229170540951) * 10^40
        + 9293178620884637756681786658142544875146) * 10^40
        + 7949776609756266975530608560298372036895) * 10^40
        + 6742879890149129601390826002527778596825) * 10^40
        + 3588168506991580573050633403360500835963) * 10^40
        + 260694438418210224956285606867030861471) * 10^40
        + 1726830863195304844720108601547024552015) * 10^40
        + 5289223622399282107779229503007454306373)) : ℚ) /
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
    ((((((((((1390276429130 * 10^40
        + 8610050261419206920217421829102716487882) * 10^40
        + 4011375901070813672686091301425473337099) * 10^40
        + 3626250847139962410169500931205588402505) * 10^40
        + 2498907042833364417796495728032598096956) * 10^40
        + 4334048661435540533301164008580000152999) * 10^40
        + 4651256845630962618174240471673183462013) * 10^40
        + 483765670475695220150286437202903278659) * 10^40
        + 338920107820200554675943855877262051563) : ℚ) /
        ((((((((10797609 * 10^40
        + 3586473984077732042708049114296486875524) * 10^40
        + 8970281936486609936035964207494624051236) * 10^40
        + 529955905854364300751554222584167967660) * 10^40
        + 44383336432906145944076110436688860061) * 10^40
        + 1615565763272992491422655305589112821870) * 10^40
        + 8825999741868268631751715784150425484683) * 10^40
        + 8633339624263947002089039881294027246696) * 10^40
        + 1172664106250138656450683306238963351552)))

noncomputable def batchN02704MinusP002Error2654 : ℝ := ((14710856534966248467 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN02704MinusP002BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP002Center2654‖ ≤ batchN02704MinusP002Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP002Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP002Input2654]
  have hs : compactExp2547 batchN02704MinusP002Input2654 8 =
      (batchN02704MinusP002Center2654, ((14710856534966248467 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP002Input2654 8).2 : ℝ) =
      batchN02704MinusP002Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP002Error2654]
  have h := compactExp_error2547 batchN02704MinusP002Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchN02704MinusP002Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP002Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP002DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP002Factor2654 * embedPair2542 batchN02704MinusP002Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP002Factor2654 : ℝ) * batchN02704MinusP002Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP002Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP002Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP002BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP002Factor2654)

def batchN02704MinusP003Input2654 : RatPair2542 := ((((-((70228 * 10^40
        + 1578618648103239365546333140061587571427) * 10^40
        + 2985539216356294380083266837386150844323)) : ℚ) /
        ((415806 * 10^40
        + 9371244809296725772723606675176446357802) * 10^40
        + 447237920754980795911929244876800000000)),
    (((-54668031270047913913566379) : ℚ) /
        115292150460684697600000000))

def batchN02704MinusP003Center2654 : RatPair2542 := ((((-102983243484972695843730390395) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-220984090002582734303232415591) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchN02704MinusP003Factor2654 : RatPair2542 :=
    ((((-(((((((((((176037168517207568054550885077472836
    *
    10^40
        + 2298563334793160016689330131238440173204) * 10^40
        + 1884948152376674346702395476626713052381) * 10^40
        + 5170798638086011822336221369664750477242) * 10^40
        + 4588760932982824098093102475642728162939) * 10^40
        + 5174026903518746450270975869229628030132) * 10^40
        + 1130312443746714407532902700773624311585) * 10^40
        + 1866593071512457725328021356974205680741) * 10^40
        + 4937999620600050343547928236361176448366) * 10^40
        + 2434030609428176886845178934392057025100) * 10^40
        + 8052569140395647523071475649199708773591) * 10^40
        + 511933512006422786339463764247154157919)) : ℚ) /
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
    (((-((((((((1379259007148409616078 * 10^40
        + 2707205963740071453144284533582928165878) * 10^40
        + 4290164298392616195887880759347751634042) * 10^40
        + 688355584211730283988101258443548246376) * 10^40
        + 4641669298704515040361885755619384676066) * 10^40
        + 6027512714338606302363701378419996302666) * 10^40
        + 5538200923736365062077255106610195748933) * 10^40
        + 2156888776662666819122203522479289195437) * 10^40
        + 2177555830978540195982291971287639630351)) : ℚ) /
        ((((((((34692676673811274 * 10^40
        + 128074125893813266840425590508825200511) * 10^40
        + 4088868557146161593343621828857606946430) * 10^40
        + 3116465880148502597479334338734333885453) * 10^40
        + 6690487160467244914226014038809137420893) * 10^40
        + 967985277916314488509526984022673398831) * 10^40
        + 1094247494220346831507178057090725668908) * 10^40
        + 4144132175624955449388270581627986533744) * 10^40
        + 5746016863812249415352748902068829290496)))

noncomputable def batchN02704MinusP003Error2654 : ℝ := ((53476660314846633286429113 : ℝ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))

theorem batchN02704MinusP003BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP003Center2654‖ ≤ batchN02704MinusP003Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP003Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP003Input2654]
  have hs : compactExp2547 batchN02704MinusP003Input2654 8 =
      (batchN02704MinusP003Center2654, ((53476660314846633286429113 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP003Input2654 8).2 : ℝ) =
      batchN02704MinusP003Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP003Error2654]
  have h := compactExp_error2547 batchN02704MinusP003Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchN02704MinusP003Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP003Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP003DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP003Factor2654 * embedPair2542 batchN02704MinusP003Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP003Factor2654 : ℝ) * batchN02704MinusP003Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP003Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP003Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP003BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP003Factor2654)

def batchN02704MinusP004Input2654 : RatPair2542 := ((((-((1213 * 10^40
        + 1156709413815825987536732349495727924044) * 10^40
        + 3431592827938250463508120344993759175849)) : ℚ) /
        ((8382 * 10^40
        + 7530312459026314251984141299542600038641) * 10^40
        + 5318978297451200742725530420838400000000)),
    ((54668031270047913913566379 : ℚ) /
        115292150460684697600000000))

def batchN02704MinusP004Center2654 : RatPair2542 := ((((-50249225686456146115974385225945) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((26956519905289865112084360768053 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN02704MinusP004Factor2654 : RatPair2542 := ((((-(((((((((((217009698974699354739314 *
    10^40
        + 8785499502272266359323281500255320252062) * 10^40
        + 5175439148649210938019932167361727193630) * 10^40
        + 4376874876611230635868435014293749902072) * 10^40
        + 2129997663529003866703938948920522711521) * 10^40
        + 3219634052480598625521509064861242477944) * 10^40
        + 5214556695314884787192715752850108234208) * 10^40
        + 1606335374606153252406509653536194531911) * 10^40
        + 6924170011742207984941854411422112852803) * 10^40
        + 5274614625848363509883603777491798659186) * 10^40
        + 1676204280632425490148002177513625303179) * 10^40
        + 6495253558433969808637402208085579306373)) : ℚ) /
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
    ((((((((((106699761180089 * 10^40
        + 819538202755765028175224368903490503299) * 10^40
        + 2093842960412756802770058164025749618945) * 10^40
        + 2180434178256910625163297582639166387833) * 10^40
        + 3421269431993138808213292612768234795570) * 10^40
        + 6386950631647372358724923923624262440478) * 10^40
        + 1893932581804743802499104444664122616756) * 10^40
        + 2160975756510648498446203042149556119905) * 10^40
        + 3820450005577494523732822843341487948437) : ℚ) /
        ((((((((1910276868 * 10^40
        + 7143605086617080012378433395487729694547) * 10^40
        + 9380410139889950991794641576550999617111) * 10^40
        + 1319557373781176227134621714215647026550) * 10^40
        + 6747846133431990198624640516214316470816) * 10^40
        + 4819251154708896951614326628589582303542) * 10^40
        + 1989429138044381900918670741501429345974) * 10^40
        + 5801300267448362710470076006840776150972) * 10^40
        + 8336703345951134713129083306238963351552)))

noncomputable def batchN02704MinusP004Error2654 : ℝ := ((203758462513469541571904517823 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN02704MinusP004BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP004Center2654‖ ≤ batchN02704MinusP004Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP004Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP004Input2654]
  have hs : compactExp2547 batchN02704MinusP004Input2654 8 =
      (batchN02704MinusP004Center2654, ((203758462513469541571904517823 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP004Input2654 8).2 : ℝ) =
      batchN02704MinusP004Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP004Error2654]
  have h := compactExp_error2547 batchN02704MinusP004Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchN02704MinusP004Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP004Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP004DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP004Factor2654 * embedPair2542 batchN02704MinusP004Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP004Factor2654 : ℝ) * batchN02704MinusP004Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP004Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP004Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP004BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP004Factor2654)

def batchN02704MinusP005Center2654 : RatPair2542 := (0, 0)

def batchN02704MinusP005Factor2654 : RatPair2542 := (0, 0)

noncomputable def batchN02704MinusP005Error2654 : ℝ := 0

theorem batchN02704MinusP005Exterior2654 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02704MinusPosition2654 = 0
        := by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |batchN02704MinusPosition2654| := by
    norm_num [storedWidth, batchN02704MinusPosition2654]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem batchN02704MinusP005BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP005Center2654‖ ≤ batchN02704MinusP005Error2654 := by
  rw [batchN02704MinusP005Exterior2654]
  norm_num [batchN02704MinusP005Center2654, batchN02704MinusP005Error2654,
      batchN02704MinusZero2654]

theorem batchN02704MinusP005DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP005Factor2654 * embedPair2542 batchN02704MinusP005Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP005Factor2654 : ℝ) * batchN02704MinusP005Error2654 :=
            by
  rw [batchN02704MinusP005Exterior2654]
  norm_num [batchN02704MinusP005Factor2654, batchN02704MinusP005Center2654,
      batchN02704MinusP005Error2654,
      batchN02704MinusZero2654, pairMagnitude2542]

def batchN02704MinusP006Input2654 : RatPair2542 := ((((-10268344805974392100986400550317) : ℚ) /
        17997946250671801739673600000000),
    ((0 : ℚ) /
        1))

def batchN02704MinusP006Center2654 : RatPair2542 := (((14068696455048369 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def batchN02704MinusP006Factor2654 : RatPair2542 := ((((((7931 * 10^40
        + 1980500373135061291170039549752461731689) * 10^40
        + 816823311994582658702521742444777487409) * 10^40
        + 4100599082318429164302981029243220082637) : ℚ) /
        ((242913578760400323024283657905529282089 * 10^40
        + 273103668815392236120585583293744315861) * 10^40
        + 4130620045995286685576151766054239338904)),
    ((0 : ℚ) /
        1))

noncomputable def batchN02704MinusP006Error2654 : ℝ := ((2301259777463 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN02704MinusP006BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP006Center2654‖ ≤ batchN02704MinusP006Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP006Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP006Input2654]
  have hs : compactExp2547 batchN02704MinusP006Input2654 7 =
      (batchN02704MinusP006Center2654, ((2301259777463 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP006Input2654 7).2 : ℝ) =
      batchN02704MinusP006Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP006Error2654]
  have h := compactExp_error2547 batchN02704MinusP006Input2654 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          batchN02704MinusP006Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP006Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP006DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP006Factor2654 * embedPair2542 batchN02704MinusP006Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP006Factor2654 : ℝ) * batchN02704MinusP006Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP006Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP006Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP006BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP006Factor2654)

def batchN02704MinusP007Input2654 : RatPair2542 := ((((-((70228 * 10^40
        + 1578618648103239365546333140061587571427) * 10^40
        + 2985539216356294380083266837386150844323)) : ℚ) /
        ((103951 * 10^40
        + 7342811202324181443180901668794111589450) * 10^40
        + 5111809480188745198977982311219200000000)),
    ((0 : ℚ) /
        1))

def batchN02704MinusP007Center2654 : RatPair2542 := (((121901103843397125307301253425 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def batchN02704MinusP007Factor2654 : RatPair2542 := ((((((((((((((1190870 * 10^40
        + 9561034293846482000051109688884443219211) * 10^40
        + 666971577734575749598382201903407779723) * 10^40
        + 9436961050579581125161272453116637927461) * 10^40
        + 8190756632334543725381978260499939223809) * 10^40
        + 4901141255893448076555512695568290720848) * 10^40
        + 4073820310324236115398192905003896638546) * 10^40
        + 8151577446631344263614375162202166417389) * 10^40
        + 697018359484459755063397118434431632254) * 10^40
        + 165152604701357160493444984954610965422) * 10^40
        + 1730974437389186251347722668682215749829) * 10^40
        + 1716247963870340117657920352774386460397) : ℚ) /
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

noncomputable def batchN02704MinusP007Error2654 : ℝ := ((8428687828913767722721185 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN02704MinusP007BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP007Center2654‖ ≤ batchN02704MinusP007Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP007Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP007Input2654]
  have hs : compactExp2547 batchN02704MinusP007Input2654 6 =
      (batchN02704MinusP007Center2654, ((8428687828913767722721185 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP007Input2654 6).2 : ℝ) =
      batchN02704MinusP007Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP007Error2654]
  have h := compactExp_error2547 batchN02704MinusP007Input2654 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          batchN02704MinusP007Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP007Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP007DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP007Factor2654 * embedPair2542 batchN02704MinusP007Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP007Factor2654 : ℝ) * batchN02704MinusP007Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP007Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP007Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP007BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP007Factor2654)

def batchN02704MinusP008Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((39371688844277275851267847 : ℚ) /
        14757395258967641292800000000))

def batchN02704MinusP008Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP008Factor2654 : RatPair2542 :=
    ((((((((((((((1206757042913577816335891218717251 *
    10^40
        + 4027565489810150746841832985233775141556) * 10^40
        + 2970990916707370425158431177063847482226) * 10^40
        + 5347955956968948702254910428172898476480) * 10^40
        + 9034414239340997350548532963558490762248) * 10^40
        + 9326362099369684767345380888002415215833) * 10^40
        + 299006218368943999032709542539133601679) * 10^40
        + 3262558909949470580909105927903504921417) * 10^40
        + 6162065588016493992719347492586509123751) * 10^40
        + 6763689201542374869735018669265768924011) * 10^40
        + 9546317457403028189952928257341419726711) * 10^40
        + 7058123657732525558548979023037661959929) : ℚ) /
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
    (((-((((((((37561646559654377147 * 10^40
        + 7484203345215461838231307325616453881866) * 10^40
        + 9494500567160483976037643061756778942904) * 10^40
        + 4888822035418425535683343004576878303799) * 10^40
        + 6769415027798662651737239760762588648329) * 10^40
        + 6071414952721107429090167809408405584503) * 10^40
        + 6663886131741846311723230810694684298815) * 10^40
        + 3299075735006552194639875847887098823356) * 10^40
        + 4081663196962953670557225044297275321019)) : ℚ) /
        ((((((((282009 * 10^40
        + 1534053747890721878994883316071335516412) * 10^40
        + 7203412894862525178913122632293423961325) * 10^40
        + 4643598740483511798171907167314555273299) * 10^40
        + 7653370293239890248041392433252686320301) * 10^40
        + 276787278843864065217788346412891156313) * 10^40
        + 3804230123880309267720806057899489492219) * 10^40
        + 4660536509913901103997583397664676183943) * 10^40
        + 4148980184670273661267873030935804903424)))

noncomputable def batchN02704MinusP008Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP008BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP008Center2654‖ ≤ batchN02704MinusP008Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP008Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP008Input2654]
  have hs : compactExp2547 batchN02704MinusP008Input2654 14 =
      (batchN02704MinusP008Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP008Input2654 14).2 : ℝ) =
      batchN02704MinusP008Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP008Error2654]
  have h := compactExp_error2547 batchN02704MinusP008Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP008Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP008Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP008DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP008Factor2654 * embedPair2542 batchN02704MinusP008Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP008Factor2654 : ℝ) * batchN02704MinusP008Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP008Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP008Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP008BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP008Factor2654)

def batchN02704MinusP009Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((58556016847187164876286361 : ℚ) /
        14757395258967641292800000000))

def batchN02704MinusP009Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP009Factor2654 : RatPair2542 :=
    ((((((((((((((1206757042634375770408202638363434 *
    10^40
        + 7432137001284193082461792253867313137045) * 10^40
        + 702000694129074850088237642325366532648) * 10^40
        + 4436424768653296449689330804259248398745) * 10^40
        + 3101686380798136661527458023488851691808) * 10^40
        + 1938908763375158340137052267435148110687) * 10^40
        + 7591543332186980070172791106719567166511) * 10^40
        + 35801721825788698251885942187586121272) * 10^40
        + 4088642046968826775880148893029579516167) * 10^40
        + 4254720039971147657099346807741892525092) * 10^40
        + 5848377515942492632648782618234237715192) * 10^40
        + 5198684278583066336304862893790049889337) : ℚ) /
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
    (((-((((((((130349356037582660156 * 10^40
        + 3760052624965567929977843790601669687189) * 10^40
        + 1549588170472013995471404286475980225364) * 10^40
        + 4345317522830302752686238057420385617651) * 10^40
        + 3216712544377948156605537875522547209635) * 10^40
        + 5287944008263957552393862493144273628359) * 10^40
        + 1100240481029135408585382068817102715798) * 10^40
        + 4278272420258062870281931590538527257031) * 10^40
        + 7164766079399276398847746821776809380481)) : ℚ) /
        ((((((((658021 * 10^40
        + 3579458745078351050988061070833116204963) * 10^40
        + 141296754679225417463952808684655909759) * 10^40
        + 4168397061128194195734450057067295637699) * 10^40
        + 4524530684226410578763249010922934747369) * 10^40
        + 645836983969016152174839474963412698064) * 10^40
        + 5543203622387388291348547468432142148512) * 10^40
        + 874585189799102575994361261217577762534) * 10^40
        + 6347620430897305209625037072183544774656)))

noncomputable def batchN02704MinusP009Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP009BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP009Center2654‖ ≤ batchN02704MinusP009Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP009Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP009Input2654]
  have hs : compactExp2547 batchN02704MinusP009Input2654 14 =
      (batchN02704MinusP009Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP009Input2654 14).2 : ℝ) =
      batchN02704MinusP009Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP009Error2654]
  have h := compactExp_error2547 batchN02704MinusP009Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP009Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP009Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP009DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP009Factor2654 * embedPair2542 batchN02704MinusP009Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP009Factor2654 : ℝ) * batchN02704MinusP009Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP009Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP009Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP009BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP009Factor2654)

def batchN02704MinusP010Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((34833351639308188388476671 : ℚ) /
        7378697629483820646400000000))

def batchN02704MinusP010Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP010Factor2654 : RatPair2542 :=
    ((((((((((((((301689260605662673007156974474749 *
    10^40
        + 7106270509530502943193813650140119780757) * 10^40
        + 5890878353995813158401870451609909386759) * 10^40
        + 7914960662206010199640524877703530748119) * 10^40
        + 3264654274720655958135102318297744959348) * 10^40
        + 9764356208349039713498138566461371674220) * 10^40
        + 3315079153264148673937338254933591657399) * 10^40
        + 6701575044124068008060379001462182920387) * 10^40
        + 4934529701266124241104748051825180848938) * 10^40
        + 8906741528947900512064636607266507175575) * 10^40
        + 4670357549852755964735394405836105220120) * 10^40
        + 8460784870969863562086897905941740337481) : ℚ) /
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
    (((-((((((((2153922763572280059 * 10^40
        + 7192483966126357516349622600858651610698) * 10^40
        + 4399727287264931453745252026192243547855) * 10^40
        + 2542299034225455252249370772574948898102) * 10^40
        + 1422123765688402499385830121851729495148) * 10^40
        + 8785078360750209712781866620517795322374) * 10^40
        + 9463111915882040227472555220986974309496) * 10^40
        + 6770701146015077241411939908173211367644) * 10^40
        + 4804824826100481963551904699832049469263)) : ℚ) /
        ((((((((9139 * 10^40
        + 1855270260348310431263723070428237725068) * 10^40
        + 9307518010481655908575888233453953554302) * 10^40
        + 2141227736960113808274089584125934661634) * 10^40
        + 7146174037280922369149489569596151871491) * 10^40
        + 2370081069221791891002428326041158509695) * 10^40
        + 3410322272533158170713174270394890863173) * 10^40
        + 7789924794302765313555477239739133024479) * 10^40
        + 6477050283762462572355903292669215899648)))

noncomputable def batchN02704MinusP010Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP010BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP010Center2654‖ ≤ batchN02704MinusP010Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP010Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP010Input2654]
  have hs : compactExp2547 batchN02704MinusP010Input2654 14 =
      (batchN02704MinusP010Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP010Input2654 14).2 : ℝ) =
      batchN02704MinusP010Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP010Error2654]
  have h := compactExp_error2547 batchN02704MinusP010Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP010Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP010Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP010DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP010Factor2654 * embedPair2542 batchN02704MinusP010Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP010Factor2654 : ℝ) * batchN02704MinusP010Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP010Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP010Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP010BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP010Factor2654)

def batchN02704MinusP011Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((38537265293058906320467951 : ℚ) /
        7378697629483820646400000000))

def batchN02704MinusP011Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP011Factor2654 : RatPair2542 :=
    ((((((((((((((301689260565274942461003418166049 *
    10^40
        + 8489390910660831079752622135759931766198) * 10^40
        + 9197652155210764899836167898616475735512) * 10^40
        + 7807908609041069611282877811001374654257) * 10^40
        + 4956835425063172850126078462493737349123) * 10^40
        + 6090908914660395940421909298137861266550) * 10^40
        + 7948457118983784318657764440518734010210) * 10^40
        + 3004263589924271640708375726808788931200) * 10^40
        + 3321322776361890184659469954291767305661) * 10^40
        + 123779528779587749086001728254742124112) * 10^40
        + 3603706422743081413103913959529653838772) * 10^40
        + 2231940558325046174636866256674197698921) : ℚ) /
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
    (((-((((((((64339772213371339407 * 10^40
        + 2057990738910847360522315644099343036762) * 10^40
        + 7377520736713700310424108840222871924349) * 10^40
        + 7915993864833900027672843200436005986467) * 10^40
        + 3277295751055695850157066933888550863765) * 10^40
        + 5603848277981143897008963807265999845496) * 10^40
        + 914559133413278782135503918963292442483) * 10^40
        + 7223394399652781199282992716542892615720) * 10^40
        + 4005692690927669692632993955730503628101)) : ℚ) /
        ((((((((246758 * 10^40
        + 92297029404381644120522901562418576861) * 10^40
        + 1302986283004709531548982303256745966159) * 10^40
        + 7813148897923072823400418771400235864137) * 10^40
        + 2946699006584903967036218379096100530263) * 10^40
        + 3992188868988381057065564803111279761774) * 10^40
        + 2078701358395270609255705300662053305692) * 10^40
        + 327969446174663465997885472956591660950) * 10^40
        + 4880357661586489453609388902068829290496)))

noncomputable def batchN02704MinusP011Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP011BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP011Center2654‖ ≤ batchN02704MinusP011Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP011Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP011Input2654]
  have hs : compactExp2547 batchN02704MinusP011Input2654 14 =
      (batchN02704MinusP011Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP011Input2654 14).2 : ℝ) =
      batchN02704MinusP011Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP011Error2654]
  have h := compactExp_error2547 batchN02704MinusP011Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP011Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP011Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP011DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP011Factor2654 * embedPair2542 batchN02704MinusP011Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP011Factor2654 : ℝ) * batchN02704MinusP011Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP011Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP011Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP011BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP011Factor2654)

def batchN02704MinusP012Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((847472267017150096839859 : ℚ) /
        147573952589676412928000000))

def batchN02704MinusP012Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP012Factor2654 : RatPair2542 := ((((((((((((((75422315129786026084162208199395
    *
    10^40
        + 5800226542492669143572438929732574417058) * 10^40
        + 9706320917101088842625300214322844682606) * 10^40
        + 8970994600893676367739908656510048540188) * 10^40
        + 6602772685581494909521836236584214844353) * 10^40
        + 7530874562397397546285624255874282065175) * 10^40
        + 5799840396817424323647630573056026196655) * 10^40
        + 5472118094193170074018906822970188268041) * 10^40
        + 297833639083506124709656600763618484580) * 10^40
        + 5613142005967904227347616813342271550476) * 10^40
        + 8228583397174250439594668572286447066668) * 10^40
        + 3481183785395204965305934300806042187553) : ℚ) /
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
    (((-((((((((8843091907511368091 * 10^40
        + 5926101551956907411571541125995559320360) * 10^40
        + 1765743805045036361411947657966128304149) * 10^40
        + 7163508543130394942414540528518028921603) * 10^40
        + 4385433153709145180324131213433092639547) * 10^40
        + 5250710077425960173827803284534803573851) * 10^40
        + 3938578865445929281611084476283405494750) * 10^40
        + 2686081280229320099382912298741875275906) * 10^40
        + 7970336512083720553904372328296267348225)) : ℚ) /
        ((((((((30844 * 10^40
        + 7511537128675547705515065362695302322107) * 10^40
        + 6412873285375588691443622787907093245769) * 10^40
        + 9726643612240384102925052346425029483017) * 10^40
        + 1618337375823112995879527297387012566282) * 10^40
        + 9249023608623547632133195600388909970221) * 10^40
        + 7759837669799408826156963162582756663211) * 10^40
        + 5040996180771832933249735684119573957618) * 10^40
        + 8110044707698311181701173612758603661312)))

noncomputable def batchN02704MinusP012Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP012BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP012Center2654‖ ≤ batchN02704MinusP012Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP012Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP012Input2654]
  have hs : compactExp2547 batchN02704MinusP012Input2654 14 =
      (batchN02704MinusP012Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP012Input2654 14).2 : ℝ) =
      batchN02704MinusP012Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP012Error2654]
  have h := compactExp_error2547 batchN02704MinusP012Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP012Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP012Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP012DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP012Factor2654 * embedPair2542 batchN02704MinusP012Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP012Factor2654 : ℝ) * batchN02704MinusP012Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP012Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP012Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP012BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP012Factor2654)

def batchN02704MinusP013Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((9173924387612369119306941 : ℚ) /
        1475739525896764129280000000))

def batchN02704MinusP013Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP013Factor2654 : RatPair2542 :=
    ((((((((((((((301689260473296110335462398752550 *
    10^40
        + 3554604014826152974080024519790573552700) * 10^40
        + 2036615263484707426163956915566738225983) * 10^40
        + 6437977702297852334253554513695292082712) * 10^40
        + 1809441088830728451214824429718181779385) * 10^40
        + 6541743593064742011436285351808916048150) * 10^40
        + 8229887365352313751877069107240422052584) * 10^40
        + 4418516143338260944178838229210954787925) * 10^40
        + 7338576628269059911046214904445355520062) * 10^40
        + 5731031998034926758934758584675432583967) * 10^40
        + 3785862904797331028338752766616771925086) * 10^40
        + 5220607184346914619813967021737519200937) : ℚ) /
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
    (((-((((((((25527161864977036907 * 10^40
        + 6817489848509709865043876078535735204008) * 10^40
        + 3197768586333005612579432458027544467215) * 10^40
        + 5748096860465721072009140776759099268279) * 10^40
        + 1718998992719465465442205139505777132697) * 10^40
        + 4684466543314750854678786851774826824558) * 10^40
        + 5526070768124078686711730243574543096340) * 10^40
        + 817979836600702710901702192156694814512) * 10^40
        + 9685614499379572387173443005863466840265)) : ℚ) /
        ((((((((82252 * 10^40
        + 6697432343134793881373507633854139525620) * 10^40
        + 3767662094334903177182994101085581988719) * 10^40
        + 9271049632641024274466806257133411954712) * 10^40
        + 4315566335528301322345406126365366843421) * 10^40
        + 1330729622996127019021854934370426587258) * 10^40
        + 692900452798423536418568433554017768564) * 10^40
        + 109323148724887821999295157652197220316) * 10^40
        + 8293452553862163151203129634022943096832)))

noncomputable def batchN02704MinusP013Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP013BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP013Center2654‖ ≤ batchN02704MinusP013Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP013Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP013Input2654]
  have hs : compactExp2547 batchN02704MinusP013Input2654 14 =
      (batchN02704MinusP013Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP013Input2654 14).2 : ℝ) =
      batchN02704MinusP013Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP013Error2654]
  have h := compactExp_error2547 batchN02704MinusP013Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP013Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP013Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP013DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP013Factor2654 * embedPair2542 batchN02704MinusP013Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP013Factor2654 : ℝ) * batchN02704MinusP013Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP013Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP013Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP013BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP013Factor2654)

def batchN02704MinusP014Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((52347367793712943072596661 : ℚ) /
        7378697629483820646400000000))

def batchN02704MinusP014Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP014Factor2654 : RatPair2542 :=
    ((((((((((((((301689260378742753913643740740602 *
    10^40
        + 2807791810163210348402209577664470428213) * 10^40
        + 8506715080526433776764360153591774624328) * 10^40
        + 7853619555224333109317674324335521455347) * 10^40
        + 7409274429214189624424039714445193364515) * 10^40
        + 188810501646595379923307036052057708763) * 10^40
        + 790518731118144185260338938600213813933) * 10^40
        + 4664967996436163452340707232657072863128) * 10^40
        + 3343440173495620627658653647174640638882) * 10^40
        + 498978587955952127026928391861136678245) * 10^40
        + 6954644506186003490963153510683097147087) * 10^40
        + 8442588012707462379194897804444098105601) : ℚ) /
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
    (((-((((((((87396386172539603584 * 10^40
        + 4274265148306185016881181764402975124119) * 10^40
        + 6612406895011574079552279844153242406907) * 10^40
        + 9418534895866855605955740864674085038200) * 10^40
        + 2315422021206831509874635818372811748913) * 10^40
        + 2230902377171086874990639907869868162966) * 10^40
        + 8013842402002129991651882301275718032161) * 10^40
        + 7672556172563226254682510072474259009443) * 10^40
        + 3695597994513317127266966747537585176751)) : ℚ) /
        ((((((((246758 * 10^40
        + 92297029404381644120522901562418576861) * 10^40
        + 1302986283004709531548982303256745966159) * 10^40
        + 7813148897923072823400418771400235864137) * 10^40
        + 2946699006584903967036218379096100530263) * 10^40
        + 3992188868988381057065564803111279761774) * 10^40
        + 2078701358395270609255705300662053305692) * 10^40
        + 327969446174663465997885472956591660950) * 10^40
        + 4880357661586489453609388902068829290496)))

noncomputable def batchN02704MinusP014Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP014BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP014Center2654‖ ≤ batchN02704MinusP014Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP014Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP014Input2654]
  have hs : compactExp2547 batchN02704MinusP014Input2654 14 =
      (batchN02704MinusP014Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP014Input2654 14).2 : ℝ) =
      batchN02704MinusP014Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP014Error2654]
  have h := compactExp_error2547 batchN02704MinusP014Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP014Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP014Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP014DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP014Factor2654 * embedPair2542 batchN02704MinusP014Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP014Factor2654 : ℝ) * batchN02704MinusP014Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP014Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP014Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP014BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP014Factor2654)

def batchN02704MinusP015Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((56988694746382884754536097 : ℚ) /
        7378697629483820646400000000))

def batchN02704MinusP015Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP015Factor2654 : RatPair2542 :=
    ((((((((((((((301689260303325273671722840204140 *
    10^40
        + 5805748018850785981994631063616562257256) * 10^40
        + 4953337248006106841292049777458713523292) * 10^40
        + 1428721092138143985088353181388043584587) * 10^40
        + 3434767535309783067783105833719220523251) * 10^40
        + 4489279823570638343191849571551098352768) * 10^40
        + 9658232199955353315018261859042177075893) * 10^40
        + 6959651185012071561413523181547875148048) * 10^40
        + 678061215643618314852345827135187841405) * 10^40
        + 2418763338798835491817516754813692954591) * 10^40
        + 4729057999305108362481812617588019427580) * 10^40
        + 6773319427533850814030379969242326278793) : ℚ) /
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
    (((-((((((((95145299244325348783 * 10^40
        + 9075666557685637687193556668619691894672) * 10^40
        + 4373792893437841094186393340629293886228) * 10^40
        + 3447359693260141448693082355289734735918) * 10^40
        + 1296797745845644295930926943445268923053) * 10^40
        + 521982958607709752009825951980396874828) * 10^40
        + 5282994285618233758747854036999443383285) * 10^40
        + 6434201038500509299850683030116353139668) * 10^40
        + 7470522631945145736379674461412522343499)) : ℚ) /
        ((((((((246758 * 10^40
        + 92297029404381644120522901562418576861) * 10^40
        + 1302986283004709531548982303256745966159) * 10^40
        + 7813148897923072823400418771400235864137) * 10^40
        + 2946699006584903967036218379096100530263) * 10^40
        + 3992188868988381057065564803111279761774) * 10^40
        + 2078701358395270609255705300662053305692) * 10^40
        + 327969446174663465997885472956591660950) * 10^40
        + 4880357661586489453609388902068829290496)))

noncomputable def batchN02704MinusP015Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP015BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP015Center2654‖ ≤ batchN02704MinusP015Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP015Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP015Input2654]
  have hs : compactExp2547 batchN02704MinusP015Input2654 14 =
      (batchN02704MinusP015Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP015Input2654 14).2 : ℝ) =
      batchN02704MinusP015Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP015Error2654]
  have h := compactExp_error2547 batchN02704MinusP015Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP015Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP015Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP015DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP015Factor2654 * embedPair2542 batchN02704MinusP015Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP015Factor2654 : ℝ) * batchN02704MinusP015Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP015Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP015Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP015BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP015Factor2654)

def batchN02704MinusP016Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((30171440028794791767436959 : ℚ) /
        3689348814741910323200000000))

def batchN02704MinusP016Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP016Factor2654 : RatPair2542 := ((((((((((((((75422315061209264309989292717542
    *
    10^40
        + 1433303553429982374989634204749323183104) * 10^40
        + 12853450930893374699953029680898754734) * 10^40
        + 7998626425870097859781195001649750426690) * 10^40
        + 3411418349519186410821368465008157249426) * 10^40
        + 9290207291430034808963825732274262718899) * 10^40
        + 6334692507082098452137801521013541326961) * 10^40
        + 5378258080194847124397508213864325741326) * 10^40
        + 9185781945051417450553778400370350972377) * 10^40
        + 3859517701616090559846627311115574552366) * 10^40
        + 9304948936149597193303907764194492597553) * 10^40
        + 1982236298803124447838345931690687259657) : ℚ) /
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
    (((-((((((((4197719540231398881 * 10^40
        + 2345535682419680467171715915013556590594) * 10^40
        + 8337648539062749286605527016394711284523) * 10^40
        + 3040296056139042468232967537348107250520) * 10^40
        + 7879393265888659096538742593879628806018) * 10^40
        + 5410580211871354744808942843447992089651) * 10^40
        + 6185124503836550705491131274437992107420) * 10^40
        + 2437146434142512300805083803668584269070) * 10^40
        + 1609946014111666067273275445868644371879)) : ℚ) /
        ((((((((10281 * 10^40
        + 5837179042891849235171688454231767440702) * 10^40
        + 5470957761791862897147874262635697748589) * 10^40
        + 9908881204080128034308350782141676494339) * 10^40
        + 539445791941037665293175765795670855427) * 10^40
        + 6416341202874515877377731866796303323407) * 10^40
        + 2586612556599802942052321054194252221070) * 10^40
        + 5013665393590610977749911894706524652539) * 10^40
        + 6036681569232770393900391204252867887104)))

noncomputable def batchN02704MinusP016Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP016BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP016Center2654‖ ≤ batchN02704MinusP016Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP016Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP016Input2654]
  have hs : compactExp2547 batchN02704MinusP016Input2654 14 =
      (batchN02704MinusP016Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP016Input2654 14).2 : ℝ) =
      batchN02704MinusP016Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP016Error2654]
  have h := compactExp_error2547 batchN02704MinusP016Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP016Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP016Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP016DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP016Factor2654 * embedPair2542 batchN02704MinusP016Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP016Factor2654 : ℝ) * batchN02704MinusP016Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP016Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP016Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP016BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP016Factor2654)

def batchN02704MinusP017Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((66858175325789869447510077 : ℚ) /
        7378697629483820646400000000))

def batchN02704MinusP017Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP017Factor2654 : RatPair2542 :=
    ((((((((((((((301689260121670942305998733282535 *
    10^40
        + 9083246985534909587295454648080897111242) * 10^40
        + 6405750068208258847313566171864095180207) * 10^40
        + 6791666733512310720412571865740826310367) * 10^40
        + 9268503687933225376742841198774499045653) * 10^40
        + 1166846434341824335510442999482286967125) * 10^40
        + 2816295458364579851220774663620048512852) * 10^40
        + 847268923004309879513121990436700389393) * 10^40
        + 4001947179221591623405899728334486754036) * 10^40
        + 1049940646984543618869096908592944849587) * 10^40
        + 9918112373816120447066627143731098009385) * 10^40
        + 4542723587388220207771065793581234963473) : ℚ) /
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
    (((-((((((((5315374287902036190 * 10^40
        + 8887019328015918295389125658460793300766) * 10^40
        + 5117923687827253948469670084407505511661) * 10^40
        + 3042501034006146153913497562571962236417) * 10^40
        + 2588728819149809870735746581945026281453) * 10^40
        + 174975694551198147198948105668915308989) * 10^40
        + 2792157233707401387479066853868240091686) * 10^40
        + 5346173812662826022187344808502382576838) * 10^40
        + 300705817480388307467737660541253644059)) : ℚ) /
        ((((((((11750 * 10^40
        + 3813918906162113411624786804836305646517) * 10^40
        + 1966808870619271882454713443012225998388) * 10^40
        + 5610149947520146324923829465304773136387) * 10^40
        + 4902223762218328760335058018052195263345) * 10^40
        + 8761532803285161002717407847767203798179) * 10^40
        + 7241842921828346219488366919079145395509) * 10^40
        + 1444189021246412545999899308236028174330) * 10^40
        + 9756207507694594735886161376288991870976)))

noncomputable def batchN02704MinusP017Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP017BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP017Center2654‖ ≤ batchN02704MinusP017Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP017Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP017Input2654]
  have hs : compactExp2547 batchN02704MinusP017Input2654 14 =
      (batchN02704MinusP017Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP017Input2654 14).2 : ℝ) =
      batchN02704MinusP017Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP017Error2654]
  have h := compactExp_error2547 batchN02704MinusP017Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP017Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP017Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP017DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP017Factor2654 * embedPair2542 batchN02704MinusP017Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP017Factor2654 : ℝ) * batchN02704MinusP017Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP017Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP017Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP017BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP017Factor2654)

def batchN02704MinusP018Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((17330367457162959994191563 : ℚ) /
        1844674407370955161600000000))

def batchN02704MinusP018Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP018Factor2654 : RatPair2542 := ((((((((((((((18855578754488595110938847312351
    *
    10^40
        + 323998785691803996887872288621641463555) * 10^40
        + 5887141365185508952622560607859543853176) * 10^40
        + 4994310326833501345847763630618876642017) * 10^40
        + 5450423687912229584961108361947772356840) * 10^40
        + 1085940611888126873529028122853706244355) * 10^40
        + 3770623450998796511805336292644376898776) * 10^40
        + 3802702887443573052647169878863754442470) * 10^40
        + 5285173088188000456517949281021922476868) * 10^40
        + 3267795727657609718272953228923249502947) * 10^40
        + 2475382503482715871562542312192010500971) * 10^40
        + 2729355953768014122318256650358298532353) : ℚ) /
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
    (((-((((((((1808366340161281976 * 10^40
        + 3987662812102925085801579669754470935162) * 10^40
        + 2184458809104108858433529086563274043783) * 10^40
        + 9465483213707139389196299633879086552133) * 10^40
        + 1019075956557115349775211972940980223025) * 10^40
        + 7200528234619023814311797258846074008535) * 10^40
        + 3788182548745322738463442398429046162716) * 10^40
        + 7111631358724042943294820708939896227186) * 10^40
        + 1428743846115384831865402398401187054801)) : ℚ) /
        ((((((((3855 * 10^40
        + 5938942141084443463189383170336912790263) * 10^40
        + 4551609160671948586430452848488386655721) * 10^40
        + 2465830451530048012865631543303128685377) * 10^40
        + 1452292171977889124484940912173376570785) * 10^40
        + 3656127951077943454016649450048613746277) * 10^40
        + 7219979708724926103269620395322844582901) * 10^40
        + 4380124522596479116656216960514946744702) * 10^40
        + 3513755588462288897712646701594825457664)))

noncomputable def batchN02704MinusP018Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP018BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP018Center2654‖ ≤ batchN02704MinusP018Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP018Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP018Input2654]
  have hs : compactExp2547 batchN02704MinusP018Input2654 14 =
      (batchN02704MinusP018Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP018Input2654 14).2 : ℝ) =
      batchN02704MinusP018Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP018Error2654]
  have h := compactExp_error2547 batchN02704MinusP018Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP018Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP018Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP018DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP018Factor2654 * embedPair2542 batchN02704MinusP018Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP018Factor2654 : ℝ) * batchN02704MinusP018Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP018Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP018Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP018BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP018Factor2654)

def batchN02704MinusP019Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((3688665669635304979192041 : ℚ) /
        368934881474191032320000000))

def batchN02704MinusP019Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP019Factor2654 : RatPair2542 := ((((((((((((((18855578748571478353596465125367
    *
    10^40
        + 8609253085019842223152088316089521496185) * 10^40
        + 4413786862768973479460847438303600403902) * 10^40
        + 7564994193638124871625690578483194548751) * 10^40
        + 4130136554330120719802153691814991954169) * 10^40
        + 2915449300830702448676953606733289344671) * 10^40
        + 304207248822838399719348719994060964649) * 10^40
        + 9104352678824864794601284944964237150910) * 10^40
        + 5998814746810889455346798613830117277111) * 10^40
        + 9009433308938287534174834460307204554530) * 10^40
        + 2925029290390365180074885673312280310414) * 10^40
        + 5486514199620377561421266579481437457457) : ℚ) /
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
    (((-((((((((213833346238825356 * 10^40
        + 6543280927008576962087645248955072161054) * 10^40
        + 7928143365562847809985318913982395496273) * 10^40
        + 3326439873467709547953545020725791072323) * 10^40
        + 1400620087054139502324104383195344248956) * 10^40
        + 668365777715553127690936922811755471021) * 10^40
        + 2965139350401062515653045911939988702280) * 10^40
        + 5463364705784452120114139081449330065881) * 10^40
        + 3973298216037535905346735102913538727055)) : ℚ) /
        ((((((((428 * 10^40
        + 3993215793453827051465487018926323643362) * 10^40
        + 6061289906741327620714494760943154072857) * 10^40
        + 9162870050170005334762847949255903187264) * 10^40
        + 1272476907997543236053882323574819618976) * 10^40
        + 1517347550119771494890738827783179305141) * 10^40
        + 9691108856524991789252180043924760509211) * 10^40
        + 2708902724732942124072912995612771860522) * 10^40
        + 4834861732051365433079182966843869495296)))

noncomputable def batchN02704MinusP019Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP019BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP019Center2654‖ ≤ batchN02704MinusP019Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP019Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP019Input2654]
  have hs : compactExp2547 batchN02704MinusP019Input2654 14 =
      (batchN02704MinusP019Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP019Input2654 14).2 : ℝ) =
      batchN02704MinusP019Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP019Error2654]
  have h := compactExp_error2547 batchN02704MinusP019Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP019Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP019Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP019DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP019Factor2654 * embedPair2542 batchN02704MinusP019Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP019Factor2654 : ℝ) * batchN02704MinusP019Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP019Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP019Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP019BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP019Factor2654)

def batchN02704MinusP020Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((78614337331324960832264269 : ℚ) /
        7378697629483820646400000000))

def batchN02704MinusP020Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP020Factor2654 : RatPair2542 :=
    ((((((((((((((301689259867507591213400960448422 *
    10^40
        + 9020176777623445454865102144513422048204) * 10^40
        + 1486778928348895332187635301131967629385) * 10^40
        + 4406424490957424494503562486219902384266) * 10^40
        + 7545436897839678343370334176925745801953) * 10^40
        + 3558946081665497736106279595621335356296) * 10^40
        + 1609826770609443991109412011422888041266) * 10^40
        + 4772456838449674562568708561109634989737) * 10^40
        + 5786626526924814901246151170570137009608) * 10^40
        + 5164735215862273024292443551064373868818) * 10^40
        + 2072884124054102379572448049987322474734) * 10^40
        + 268410687800467996321831653397211568561) : ℚ) /
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
    (((-((((((((18750046283917807324 * 10^40
        + 1590579583827521723817993724980406149411) * 10^40
        + 9119056843078333547207043269471572054238) * 10^40
        + 6935681251076487116775419533033097769576) * 10^40
        + 8688388044408071865225544057596589474552) * 10^40
        + 1533519969363237032121068386274951461449) * 10^40
        + 9167675455053077624958900810257444445984) * 10^40
        + 6879288132766121628129022545328915292608) * 10^40
        + 350146570827731025451285112728080078657)) : ℚ) /
        ((((((((35251 * 10^40
        + 1441756718486340234874360414508916939551) * 10^40
        + 5900426611857815647364140329036677995165) * 10^40
        + 6830449842560438974771488395914319409162) * 10^40
        + 4706671286654986281005174054156585790037) * 10^40
        + 6284598409855483008152223543301611394539) * 10^40
        + 1725528765485038658465100757237436186527) * 10^40
        + 4332567063739237637999697924708084522992) * 10^40
        + 9268622523083784207658484128866975612928)))

noncomputable def batchN02704MinusP020Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP020BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP020Center2654‖ ≤ batchN02704MinusP020Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP020Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP020Input2654]
  have hs : compactExp2547 batchN02704MinusP020Input2654 14 =
      (batchN02704MinusP020Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP020Input2654 14).2 : ℝ) =
      batchN02704MinusP020Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP020Error2654]
  have h := compactExp_error2547 batchN02704MinusP020Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP020Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP020Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP020DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP020Factor2654 * embedPair2542 batchN02704MinusP020Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP020Factor2654 : ℝ) * batchN02704MinusP020Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP020Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP020Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP020BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP020Factor2654)

def batchN02704MinusP021Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((82654361045867903481379437 : ℚ) /
        7378697629483820646400000000))

def batchN02704MinusP021Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP021Factor2654 : RatPair2542 :=
    ((((((((((((((301689259770679711810897830232937 *
    10^40
        + 3262706945899471355097628298771382014875) * 10^40
        + 2569864298625241287834661863470434935957) * 10^40
        + 9702096190140367752860209375035465119150) * 10^40
        + 7494012488874101933513671181639447123646) * 10^40
        + 4126418520069070891928841969743462248392) * 10^40
        + 2187996479221264985201437778870758255893) * 10^40
        + 7606364391734303786775117075810994932556) * 10^40
        + 4990744526958218500437116666332231172833) * 10^40
        + 3113177323403091098172667262581273910458) * 10^40
        + 7824134540248086705227226315964627092669) * 10^40
        + 8883603485916635388438168583580553006833) : ℚ) /
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
    (((-((((((((45998444364059347600 * 10^40
        + 4452918685400979543115769436633137356693) * 10^40
        + 2674251203684530920503409416338081774594) * 10^40
        + 7293739924567988299613245766299763938240) * 10^40
        + 8375739668135290347145771052995010454789) * 10^40
        + 8670062786334691228431784566492991483816) * 10^40
        + 3523151910535449833593070780579408864005) * 10^40
        + 9657895655915696538303848553318054727812) * 10^40
        + 5406526214880364471609830348568729546573)) : ℚ) /
        ((((((((82252 * 10^40
        + 6697432343134793881373507633854139525620) * 10^40
        + 3767662094334903177182994101085581988719) * 10^40
        + 9271049632641024274466806257133411954712) * 10^40
        + 4315566335528301322345406126365366843421) * 10^40
        + 1330729622996127019021854934370426587258) * 10^40
        + 692900452798423536418568433554017768564) * 10^40
        + 109323148724887821999295157652197220316) * 10^40
        + 8293452553862163151203129634022943096832)))

noncomputable def batchN02704MinusP021Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP021BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP021Center2654‖ ≤ batchN02704MinusP021Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP021Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP021Input2654]
  have hs : compactExp2547 batchN02704MinusP021Input2654 14 =
      (batchN02704MinusP021Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP021Input2654 14).2 : ℝ) =
      batchN02704MinusP021Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP021Error2654]
  have h := compactExp_error2547 batchN02704MinusP021Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP021Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP021Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP021DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP021Factor2654 * embedPair2542 batchN02704MinusP021Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP021Factor2654 : ℝ) * batchN02704MinusP021Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP021Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP021Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP021BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP021Factor2654)

def batchN02704MinusP022Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((16944438833431689477671183 : ℚ) /
        1475739525896764129280000000))

def batchN02704MinusP022Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP022Factor2654 : RatPair2542 :=
    ((((((((((((((301689259719242604359495611148731 *
    10^40
        + 6124433682766828744153758052252019444099) * 10^40
        + 2367559121437095747367258108954768661331) * 10^40
        + 4528019185216282584557520722688685944464) * 10^40
        + 9146173169446715461054622620211577133819) * 10^40
        + 8372390508631246684962465505001737931330) * 10^40
        + 8797732028597731173267795618837746381318) * 10^40
        + 2164928021402598884636795889765424412003) * 10^40
        + 9024811429530395380798296336954796896767) * 10^40
        + 492110856848422173869103459889111307759) * 10^40
        + 6430932275416982911943632935696665075883) * 10^40
        + 7421917356642936272516081048734410772737) : ℚ) /
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
    (((-((((((((141447677487796708252 * 10^40
        + 6473392040436600678588390060379068956668) * 10^40
        + 5029097990356120809547401870018016470005) * 10^40
        + 5665412480542413083215128159793581171884) * 10^40
        + 8642378238857451515508390167457004406530) * 10^40
        + 3268222727284181374798917369548669429038) * 10^40
        + 4766143763513016364802282518914402000143) * 10^40
        + 4846962878035707450770309553453933355182) * 10^40
        + 7789872996628253846705831407876468981585)) : ℚ) /
        ((((((((246758 * 10^40
        + 92297029404381644120522901562418576861) * 10^40
        + 1302986283004709531548982303256745966159) * 10^40
        + 7813148897923072823400418771400235864137) * 10^40
        + 2946699006584903967036218379096100530263) * 10^40
        + 3992188868988381057065564803111279761774) * 10^40
        + 2078701358395270609255705300662053305692) * 10^40
        + 327969446174663465997885472956591660950) * 10^40
        + 4880357661586489453609388902068829290496)))

noncomputable def batchN02704MinusP022Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP022BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP022Center2654‖ ≤ batchN02704MinusP022Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP022Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP022Input2654]
  have hs : compactExp2547 batchN02704MinusP022Input2654 14 =
      (batchN02704MinusP022Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP022Input2654 14).2 : ℝ) =
      batchN02704MinusP022Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP022Error2654]
  have h := compactExp_error2547 batchN02704MinusP022Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP022Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP022Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP022DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP022Factor2654 * embedPair2542 batchN02704MinusP022Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP022Factor2654 : ℝ) * batchN02704MinusP022Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP022Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP022Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP022BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP022Factor2654)

def batchN02704MinusP023Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((45342070652492160469014283 : ℚ) /
        3689348814741910323200000000))

def batchN02704MinusP023Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP023Factor2654 : RatPair2542 := ((((((((((((((75422314890956284742142453538135
    *
    10^40
        + 2533668936543131750620840789130993062510) * 10^40
        + 5574054224436172407188782039734339512365) * 10^40
        + 6313098854777952217170765003249774355087) * 10^40
        + 1498946461672275643723233153331253213959) * 10^40
        + 3895188637539277655466446269138162407667) * 10^40
        + 9290403759853852126045791713790669348906) * 10^40
        + 6270032355897006672298435620272837229321) * 10^40
        + 4840788451990849266654217111656813209454) * 10^40
        + 67178700244875466743974858721299739850) * 10^40
        + 7422072999551205370774214646817351878768) * 10^40
        + 8707685253030742408622163565726732512129) : ℚ) /
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
    (((-((((((((18925178487651188881 * 10^40
        + 6693021391127880699659997734980159997466) * 10^40
        + 2412586323993324059425384371806042786363) * 10^40
        + 2218247717181749643739818821715055766023) * 10^40
        + 2057539137022812601919347638935048958619) * 10^40
        + 1014668225392650339062948915820490471253) * 10^40
        + 2379880666779761701696519048744728260026) * 10^40
        + 7807423906008578280538390497252639332107) * 10^40
        + 6738740586140376778844431857443933326097)) : ℚ) /
        ((((((((30844 * 10^40
        + 7511537128675547705515065362695302322107) * 10^40
        + 6412873285375588691443622787907093245769) * 10^40
        + 9726643612240384102925052346425029483017) * 10^40
        + 1618337375823112995879527297387012566282) * 10^40
        + 9249023608623547632133195600388909970221) * 10^40
        + 7759837669799408826156963162582756663211) * 10^40
        + 5040996180771832933249735684119573957618) * 10^40
        + 8110044707698311181701173612758603661312)))

noncomputable def batchN02704MinusP023Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP023BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP023Center2654‖ ≤ batchN02704MinusP023Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP023Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP023Input2654]
  have hs : compactExp2547 batchN02704MinusP023Input2654 14 =
      (batchN02704MinusP023Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP023Input2654 14).2 : ℝ) =
      batchN02704MinusP023Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP023Error2654]
  have h := compactExp_error2547 batchN02704MinusP023Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP023Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP023Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP023DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP023Factor2654 * embedPair2542 batchN02704MinusP023Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP023Factor2654 : ℝ) * batchN02704MinusP023Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP023Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP023Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP023BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP023Factor2654)

def batchN02704MinusP024Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((46712005387750232020650197 : ℚ) /
        3689348814741910323200000000))

def batchN02704MinusP024Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP024Factor2654 : RatPair2542 := ((((((((((((((75422314872214569874717079214594
    *
    10^40
        + 4482858573669842745279287486117942005620) * 10^40
        + 30040759133260908312852380507911281606) * 10^40
        + 1895523074485554688771208223121163163481) * 10^40
        + 9380734561526310642765404914586144817738) * 10^40
        + 2429234488759605594028555825517868675596) * 10^40
        + 8553206434475910056838367507373991507664) * 10^40
        + 2843923683461474750356903251043324843411) * 10^40
        + 8495524525630219833042927518771640663532) * 10^40
        + 1921015357415153852304697529521693510319) * 10^40
        + 4728407269991979611547247840434614595485) * 10^40
        + 5470128096432489992973847840815195756609) : ℚ) /
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
    (((-((((((((19496971063149056209 * 10^40
        + 4225194922533408230995081148920936266605) * 10^40
        + 8094052183832476699433130375615277114926) * 10^40
        + 8030417810980135136182013290997445306462) * 10^40
        + 893588540453348273517862917386999259213) * 10^40
        + 1732938892848961192309615958678786545227) * 10^40
        + 2513668299525209043470261300704898707675) * 10^40
        + 2055845809386813557488451979641723090789) * 10^40
        + 410839165625406711130050128782878013903)) : ℚ) /
        ((((((((30844 * 10^40
        + 7511537128675547705515065362695302322107) * 10^40
        + 6412873285375588691443622787907093245769) * 10^40
        + 9726643612240384102925052346425029483017) * 10^40
        + 1618337375823112995879527297387012566282) * 10^40
        + 9249023608623547632133195600388909970221) * 10^40
        + 7759837669799408826156963162582756663211) * 10^40
        + 5040996180771832933249735684119573957618) * 10^40
        + 8110044707698311181701173612758603661312)))

noncomputable def batchN02704MinusP024Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP024BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP024Center2654‖ ≤ batchN02704MinusP024Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP024Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP024Input2654]
  have hs : compactExp2547 batchN02704MinusP024Input2654 14 =
      (batchN02704MinusP024Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP024Input2654 14).2 : ℝ) =
      batchN02704MinusP024Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP024Error2654]
  have h := compactExp_error2547 batchN02704MinusP024Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP024Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP024Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP024DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP024Factor2654 * embedPair2542 batchN02704MinusP024Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP024Factor2654 : ℝ) * batchN02704MinusP024Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP024Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP024Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP024BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP024Factor2654)

def batchN02704MinusP025Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((1513426630246391746815783 : ℚ) /
        115292150460684697600000000))

def batchN02704MinusP025Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP025Factor2654 : RatPair2542 := ((((((((((((((73654604343679424425956628231 *
    10^40
        + 2017154976904807210477735917747116386325) * 10^40
        + 3374302000746111386663344795713290320559) * 10^40
        + 8359825133517748136888635175986088116321) * 10^40
        + 7407036459439824888079119050379054722095) * 10^40
        + 2932753821149438113432632214953969359948) * 10^40
        + 7706702899633138782694031377267493795600) * 10^40
        + 4463662669884967506642229275350265437697) * 10^40
        + 4652392192721151818130558225684118223948) * 10^40
        + 3321983496733242027179279700700333181872) * 10^40
        + 2805535059704076064063078576644714130907) * 10^40
        + 8971865677351066621427372735541481958073) : ℚ) /
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
    (((-((((((((4196456396601 * 10^40
        + 6731979451281479955403585618837087554219) * 10^40
        + 3446546955288209880960341285290208723302) * 10^40
        + 9328453237272780235891276542135236078985) * 10^40
        + 5461949729578385887824180377158368256722) * 10^40
        + 3907064450225134582940258192345007771633) * 10^40
        + 1628609374909216385640845540319056080466) * 10^40
        + 2496144085121088096887772910862044205399) * 10^40
        + 9559095109310987965174972546516853843183)) : ℚ) /
        (((((((64034496808137164586427756602044697519 * 10^40
        + 3822136997118743144047264346920254850238) * 10^40
        + 2542139113371684221619919326689292528846) * 10^40
        + 2700911877345364280879843758205968612777) * 10^40
        + 3085162986500769089377813457711273066495) * 10^40
        + 5129240440283051533478992728297053243988) * 10^40
        + 7976015060527813092047852652358631807615) * 10^40
        + 1026758333591737853238098082494123343872)))

noncomputable def batchN02704MinusP025Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP025BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP025Center2654‖ ≤ batchN02704MinusP025Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP025Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP025Input2654]
  have hs : compactExp2547 batchN02704MinusP025Input2654 14 =
      (batchN02704MinusP025Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP025Input2654 14).2 : ℝ) =
      batchN02704MinusP025Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP025Error2654]
  have h := compactExp_error2547 batchN02704MinusP025Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP025Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP025Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP025DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP025Factor2654 * embedPair2542 batchN02704MinusP025Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP025Factor2654 : ℝ) * batchN02704MinusP025Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP025Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP025Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP025BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP025Factor2654)

def batchN02704MinusP026Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((3136563586529957941722987 : ℚ) /
        230584300921369395200000000))

def batchN02704MinusP026Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP026Factor2654 : RatPair2542 := ((((((((((((((294618417274224776146198394234 *
    10^40
        + 9430826162860613219516163374033414605358) * 10^40
        + 5470209664276744500163796222273928225013) * 10^40
        + 9531209014450710538833904205845200902010) * 10^40
        + 6909335247145336972996030350326488912043) * 10^40
        + 3043798617868189986009931393244225041176) * 10^40
        + 3296758379744302002048404161625033603739) * 10^40
        + 8248313542112587328078569564106783670382) * 10^40
        + 9426536527888095958751632797623664484788) * 10^40
        + 8571420546642464521302613911498869356072) * 10^40
        + 7753272718900982551604021662742256342592) * 10^40
        + 6218284092391940362953667630055937833409) : ℚ) /
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
    (((-((((((((1704635430781603 * 10^40
        + 1005959687308953418336762538068586063865) * 10^40
        + 5542318885412275902102267953061499420222) * 10^40
        + 1163100188302808935645825306735881603761) * 10^40
        + 7565783741911741511013990855920367878828) * 10^40
        + 3807366509605996790818743497199144953385) * 10^40
        + 7848224864203595112759526980942108632971) * 10^40
        + 1966904765264217296868524254982084271753) * 10^40
        + 4980942120373124795108589984547269220731)) : ℚ) /
        ((((((((2 * 10^40
        + 5101522748789768517879680588001521427597) * 10^40
        + 8277702870547312466527623992739901293395) * 10^40
        + 6518532441700214875008376062202671307737) * 10^40
        + 8757455919382798104898753216739696208704) * 10^40
        + 9383890708301483036102875422819042066241) * 10^40
        + 662252590956201123765149492444871643608) * 10^40
        + 6597903726902732082758239724583668585120) * 10^40
        + 2489266767961238469334448337696350797824)))

noncomputable def batchN02704MinusP026Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP026BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP026Center2654‖ ≤ batchN02704MinusP026Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP026Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP026Input2654]
  have hs : compactExp2547 batchN02704MinusP026Input2654 14 =
      (batchN02704MinusP026Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP026Input2654 14).2 : ℝ) =
      batchN02704MinusP026Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP026Error2654]
  have h := compactExp_error2547 batchN02704MinusP026Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP026Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP026Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP026DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP026Factor2654 * embedPair2542 batchN02704MinusP026Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP026Factor2654 : ℝ) * batchN02704MinusP026Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP026Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP026Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP026BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP026Factor2654)

def batchN02704MinusP027Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((6589758326498808710472677 : ℚ) /
        461168601842738790400000000))

def batchN02704MinusP027Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP027Factor2654 : RatPair2542 := ((((((((((((((1178473668491616110476211366641
    * 10^40
        + 3942877516928112084121127842490366718714) * 10^40
        + 2354273701686136631297019800481353417224) * 10^40
        + 5173673531098358037620447597225745659741) * 10^40
        + 7716142428551762787643163632965994729657) * 10^40
        + 2082026435367563822886641316078549968522) * 10^40
        + 6950743695879802661226238219413050751909) * 10^40
        + 179284541740313940443315506590164690820) * 10^40
        + 4069011001389005707616775088630960365604) * 10^40
        + 832295097538159584192826524631037094125) * 10^40
        + 6876857062961803233172388390233687083213) * 10^40
        + 7236053980933773012398336080164079769313) : ℚ) /
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
    (((-((((((((42976213476065824 * 10^40
        + 618614476251169299594070209599118083542) * 10^40
        + 4610462345801002842358672134936928201902) * 10^40
        + 2164938770074908982846805961885786921161) * 10^40
        + 1187299757467558768234590137170728291942) * 10^40
        + 8032747641199419580400150510273654970558) * 10^40
        + 7081239228106602590204621077172672979996) * 10^40
        + 7811203543765330269078175567158686519117) * 10^40
        + 2007512596024309624505887333746845467999)) : ℚ) /
        ((((((((60 * 10^40
        + 2436545970954444429112334112036514262347) * 10^40
        + 8664868893135499196662975825757631041495) * 10^40
        + 6444778600805157000201025492864111385709) * 10^40
        + 178942065187154517570077201752709008918) * 10^40
        + 5213376999235592866469010147657009589785) * 10^40
        + 5894062182948826970363587818676919446607) * 10^40
        + 8349689445665569986197753390008046042885) * 10^40
        + 9742402431069723264026760104712419147776)))

noncomputable def batchN02704MinusP027Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP027BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP027Center2654‖ ≤ batchN02704MinusP027Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP027Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP027Input2654]
  have hs : compactExp2547 batchN02704MinusP027Input2654 14 =
      (batchN02704MinusP027Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP027Input2654 14).2 : ℝ) =
      batchN02704MinusP027Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP027Error2654]
  have h := compactExp_error2547 batchN02704MinusP027Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP027Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP027Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP027DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP027Factor2654 * embedPair2542 batchN02704MinusP027Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP027Factor2654 : ℝ) * batchN02704MinusP027Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP027Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP027Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP027BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP027Factor2654)

def batchN02704MinusP028Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((26860467825486442936697777 : ℚ) /
        1844674407370955161600000000))

def batchN02704MinusP028Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP028Factor2654 : RatPair2542 := ((((((((((((((18855578691899869246445342645970
    *
    10^40
        + 5498558528180165030417813713040560024503) * 10^40
        + 8716115251655787261487736958662755162810) * 10^40
        + 3450193430420738779804743757696404700120) * 10^40
        + 7178683176209832908646735808510977308026) * 10^40
        + 3950663946539698904263646534818552747563) * 10^40
        + 1063692497369865627014610078990379483174) * 10^40
        + 143660987462009203118721770876205971380) * 10^40
        + 3311137595489335833650574086473965553624) * 10^40
        + 4879146434325665839131182053163350709646) * 10^40
        + 8601765568532306586120331455917149707711) * 10^40
        + 6683026608801736025038195799018599617193) : ℚ) /
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
    (((-((((((((2802800690680765799 * 10^40
        + 3781885077080659646514508499869589401794) * 10^40
        + 2204876250187167282127442068335638368841) * 10^40
        + 4769533187046046245571258283185453763780) * 10^40
        + 6006521238266114718211146704907673032312) * 10^40
        + 8865186675284954740217156781733168270055) * 10^40
        + 9608462982554951623100013625572570125472) * 10^40
        + 8977907133031887695768038376375929484811) * 10^40
        + 1747244113807251341609166782967428259419)) : ℚ) /
        ((((((((3855 * 10^40
        + 5938942141084443463189383170336912790263) * 10^40
        + 4551609160671948586430452848488386655721) * 10^40
        + 2465830451530048012865631543303128685377) * 10^40
        + 1452292171977889124484940912173376570785) * 10^40
        + 3656127951077943454016649450048613746277) * 10^40
        + 7219979708724926103269620395322844582901) * 10^40
        + 4380124522596479116656216960514946744702) * 10^40
        + 3513755588462288897712646701594825457664)))

noncomputable def batchN02704MinusP028Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP028BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP028Center2654‖ ≤ batchN02704MinusP028Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP028Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP028Input2654]
  have hs : compactExp2547 batchN02704MinusP028Input2654 14 =
      (batchN02704MinusP028Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP028Input2654 14).2 : ℝ) =
      batchN02704MinusP028Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP028Error2654]
  have h := compactExp_error2547 batchN02704MinusP028Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP028Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP028Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP028DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP028Factor2654 * embedPair2542 batchN02704MinusP028Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP028Factor2654 : ℝ) * batchN02704MinusP028Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP028Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP028Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP028BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP028Factor2654)

def batchN02704MinusP029Input2654 : RatPair2542 := ((((-((24087 * 10^40
        + 7307773601436191432875970796606007617603) * 10^40
        + 2909722657673072448162864720686932094323)) : ℚ) /
        ((43459 * 10^40
        + 338231902943130156291582132123292714154) * 10^40
        + 9741217576934962938363471672115200000000)),
    ((27623869687037674802636509 : ℚ) /
        1844674407370955161600000000))

def batchN02704MinusP029Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02704MinusP029Factor2654 : RatPair2542 := ((((((((((((((18855578685718405667521237141469
    *
    10^40
        + 2918513637831782539427830279929824988570) * 10^40
        + 2270702782906929296562370743646997004243) * 10^40
        + 6442137085202828710372737730227658331215) * 10^40
        + 9834511636520259661890328004411141037248) * 10^40
        + 9448654249825227149386918061586360397578) * 10^40
        + 1515030214136596952291472723424672045111) * 10^40
        + 9233400764908348743529982650610041253319) * 10^40
        + 1207326732617667305361360504911126406672) * 10^40
        + 4431818757148428531965757529777241694199) * 10^40
        + 9366962477005112213424395671026070864035) * 10^40
        + 2202001564155569418219589708470865236561) : ℚ) /
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
    (((-((((((((2882459141751136590 * 10^40
        + 9206079556798839813261494385358261491216) * 10^40
        + 1029127505152577956043306826251389689860) * 10^40
        + 9060223023105285166268442032467658504107) * 10^40
        + 5052547979307375150054479930864751772767) * 10^40
        + 2958476382694097570990716945884978796854) * 10^40
        + 9593220156410217983695728206114672349996) * 10^40
        + 4207659083240250584740935886356743410757) * 10^40
        + 6197397456390298984775698704937198879959)) : ℚ) /
        ((((((((3855 * 10^40
        + 5938942141084443463189383170336912790263) * 10^40
        + 4551609160671948586430452848488386655721) * 10^40
        + 2465830451530048012865631543303128685377) * 10^40
        + 1452292171977889124484940912173376570785) * 10^40
        + 3656127951077943454016649450048613746277) * 10^40
        + 7219979708724926103269620395322844582901) * 10^40
        + 4380124522596479116656216960514946744702) * 10^40
        + 3513755588462288897712646701594825457664)))

noncomputable def batchN02704MinusP029Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02704MinusP029BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP029Center2654‖ ≤ batchN02704MinusP029Error2654 := by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchN02704MinusP029Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02704MinusP029Input2654]
  have hs : compactExp2547 batchN02704MinusP029Input2654 14 =
      (batchN02704MinusP029Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02704MinusP029Input2654 14).2 : ℝ) =
      batchN02704MinusP029Error2654 := by
    rw [hs]
    norm_num [batchN02704MinusP029Error2654]
  have h := compactExp_error2547 batchN02704MinusP029Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      batchN02704MinusPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02704MinusP029Input2654) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02704MinusPosition2654, storedWidth, nodeModulation2541,
      embedPair2542, batchN02704MinusP029Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02704MinusP029DerivativeError2654 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02704MinusPosition2654 -
      embedPair2542 batchN02704MinusP029Factor2654 * embedPair2542 batchN02704MinusP029Center2654‖
          ≤
        (pairMagnitude2542 batchN02704MinusP029Factor2654 : ℝ) * batchN02704MinusP029Error2654 :=
            by
  have hx : |batchN02704MinusPosition2654| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchN02704MinusPosition2654, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchN02704MinusPosition2654 = embedPair2542
          batchN02704MinusP029Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02704MinusPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchN02704MinusP029Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02704MinusP029BaseError2654
    (embedPair_magnitude2542 batchN02704MinusP029Factor2654)

theorem batchN02704MinusGrid2654 :
    -stripRadius2303 + (2704 : ℝ) * (2 * stripRadius2303 / 10240) =
      batchN02704MinusPosition2654 := by
  norm_num [stripRadius2303, batchN02704MinusPosition2654]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchN02704MinusP000DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP001DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP002DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP003DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP004DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP005DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP006DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP007DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP008DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP009DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP010DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP011DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP012DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP013DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP014DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP015DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP016DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP017DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP018DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP019DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP020DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP021DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP022DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP023DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP024DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP025DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP026DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP027DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP028DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusP029DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchN02704MinusGrid2654
