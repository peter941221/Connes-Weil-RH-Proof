import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchN02703MinusPosition2558 : ℝ := (((-158400514417) : ℝ) /
        51200000000)

theorem batchN02703MinusZero2558 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchN02703MinusP000Center2558 : RatPair2542 := (0, 0)

def batchN02703MinusP000Factor2558 : RatPair2542 := (0, 0)

noncomputable def batchN02703MinusP000Error2558 : ℝ := 0

theorem batchN02703MinusP000Exterior2558 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02703MinusPosition2558 = 0
        := by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |batchN02703MinusPosition2558| := by
    norm_num [storedWidth, batchN02703MinusPosition2558]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem batchN02703MinusP000BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP000Center2558‖ ≤ batchN02703MinusP000Error2558 := by
  rw [batchN02703MinusP000Exterior2558]
  norm_num [batchN02703MinusP000Center2558, batchN02703MinusP000Error2558,
      batchN02703MinusZero2558]

theorem batchN02703MinusP000DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨0, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP000Factor2558 * embedPair2542 batchN02703MinusP000Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP000Factor2558 : ℝ) * batchN02703MinusP000Error2558 :=
            by
  rw [batchN02703MinusP000Exterior2558]
  norm_num [batchN02703MinusP000Factor2558, batchN02703MinusP000Center2558,
      batchN02703MinusP000Error2558,
      batchN02703MinusZero2558, pairMagnitude2542]

def batchN02703MinusP001Input2558 : RatPair2542 := ((((-((334 * 10^40
        + 3964799398326123205247732121693677107446) * 10^40
        + 6770193440221610479362399611030126300847)) : ℚ) /
        ((949 * 10^40
        + 5678772037045116961918709892218078778647) * 10^40
        + 478078034072945845341163828019200000000)),
    ((875050540262952370391324093 : ℚ) /
        3689348814741910323200000000))

def batchN02703MinusP001Center2558 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN02703MinusP001Factor2558 : RatPair2542 := ((((((((((((((2798954425177 * 10^40
        + 640001946549554779637987802303958382842) * 10^40
        + 1828539941128642721119377257924176838277) * 10^40
        + 5391834231440568058194657441890180191819) * 10^40
        + 829210265654083132213482681565976031068) * 10^40
        + 4304241979589556603511504459330866577482) * 10^40
        + 7165342411609425308341612762428862547683) * 10^40
        + 9281548223313842843601631773385662950690) * 10^40
        + 9482136232652648697024593205925280916143) * 10^40
        + 8107448336879100558219469868103527887215) * 10^40
        + 9792906369874299178718132003483704611582) * 10^40
        + 4464834706211579283577127846616250802107) : ℚ) /
        (((((((((((13982 * 10^40
        + 5431888556776868524694846687742555711482) * 10^40
        + 3643539874405671138191136022276894766099) * 10^40
        + 1063381222825616924578099568623265074841) * 10^40
        + 307340582860131724876045024138828481384) * 10^40
        + 3433522266080022916343058469533311800933) * 10^40
        + 6433598022746643538247543670351068985409) * 10^40
        + 4901618157747804916729600365128811023350) * 10^40
        + 6572191782905580683540451751169125406456) * 10^40
        + 3109948263381595902474993232136947165560) * 10^40
        + 2515051343142866628766567001969536089169) * 10^40
        + 9074353131060105475013896551909963071488)),
    (((-((((((((12323490 * 10^40
        + 5938413647862104255341454531725350572897) * 10^40
        + 2732862333179689606402753108505981934261) * 10^40
        + 6137773490952349170035764604999468029616) * 10^40
        + 7289673125465752761206010679847319422208) * 10^40
        + 9241000728799269556505838986319681067157) * 10^40
        + 3815932107180826853400499272991631399837) * 10^40
        + 7335180776354091398585135373948317541532) * 10^40
        + 4426483165529030401247628580976992094443)) : ℚ) /
        (((((((2999533911072061356178334933236700797585 * 10^40
        + 3872345074966712881075823463820327595663) * 10^40
        + 6080942078488414962293422352759527481113) * 10^40
        + 1924315816474919185171148181808049163550) * 10^40
        + 7254513374318531456237756042013135869999) * 10^40
        + 7216795305254864798901112656239051496622) * 10^40
        + 6470262671951252419437763136236879659692) * 10^40
        + 9476927576756072039403060696143544451072)))

noncomputable def batchN02703MinusP001Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP001BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP001Center2558‖ ≤ batchN02703MinusP001Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP001Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP001Input2558]
  have hs : compactExp2547 batchN02703MinusP001Input2558 9 =
      (batchN02703MinusP001Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP001Input2558 9).2 : ℝ) =
      batchN02703MinusP001Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP001Error2558]
  have h := compactExp_error2547 batchN02703MinusP001Input2558 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          batchN02703MinusP001Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP001Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP001DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨1, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP001Factor2558 * embedPair2542 batchN02703MinusP001Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP001Factor2558 : ℝ) * batchN02703MinusP001Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP001Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP001Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP001BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP001Factor2558)

def batchN02703MinusP002Input2558 : RatPair2542 := ((((-((8589 * 10^40
        + 9586772195308868683427274465402369322489) * 10^40
        + 6038857346448285049803753288048182922927)) : ℚ) /
        ((36744 * 10^40
        + 1879937388438218950297983988018634857015) * 10^40
        + 2724428396649426762729310624153600000000)),
    (((-875050540262952370391324093) : ℚ) /
        1844674407370955161600000000))

def batchN02703MinusP002Center2558 : RatPair2542 := ((((-6970437208017745221721) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-1648025687177071950569) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)))

def batchN02703MinusP002Factor2558 : RatPair2542 := ((((-(((((((((((387491292845517818665 * 10^40
        + 980260371050687457401377465793781331339) * 10^40
        + 6905062355539959075999668161829924335845) * 10^40
        + 1253239564152587604434657574798813433708) * 10^40
        + 4065404445354374172299399366990926767499) * 10^40
        + 3554394195743342773814911897285672938478) * 10^40
        + 1838952511727080137013110843790637500998) * 10^40
        + 1654353370617362604955660843851168789137) * 10^40
        + 8556649239520347455610338653086858390626) * 10^40
        + 1606651465443360765747503549743534299009) * 10^40
        + 7049969214879016557254576190967361096839) * 10^40
        + 1865212888285073851300092475539567059013)) : ℚ) /
        (((((((((((3004290902754201 * 10^40
        + 9890420656602381934546251520975223428420) * 10^40
        + 5312068476429704922433476019333656057203) * 10^40
        + 5871967366529948449909330531669360688313) * 10^40
        + 440240840146944949528186443229530593556) * 10^40
        + 9045225124615983131617085428331830099294) * 10^40
        + 8392347465620634390281886187361670512027) * 10^40
        + 1899480248815290706121210720129639307779) * 10^40
        + 2570637387505650979219894574314308426220) * 10^40
        + 7393449775089832071856977719026125444296) * 10^40
        + 9817618164234421983396720289434654634148) * 10^40
        + 7279140922162777575737848663002377617408)),
    ((((((((((1394441592055 * 10^40
        + 1443593360263732241229099001309221367496) * 10^40
        + 6408449774328294819082048807962728113935) * 10^40
        + 961519453308959684844156653307150729132) * 10^40
        + 5572982969974966327409632066735016637710) * 10^40
        + 2637908101370088140237632602456884228732) * 10^40
        + 1409821966667958485416041995566704947118) * 10^40
        + 8806496580340691801862031114387180995617) * 10^40
        + 725159693058908182593799301433930713323) : ℚ) /
        ((((((((10760298 * 10^40
        + 4794793877505187311312115995923165650180) * 10^40
        + 1540122975001279906354463112515517416477) * 10^40
        + 9815100768799576146044201087097795319591) * 10^40
        + 785797639286362751068262139329409022437) * 10^40
        + 5482430912569833462851541391004309861102) * 10^40
        + 3829681708045944720780891948354120750175) * 10^40
        + 4448577172278033069840213133885275268078) * 10^40
        + 3410563510592266034262582463329145454592)))

noncomputable def batchN02703MinusP002Error2558 : ℝ := ((13890051478555904937 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN02703MinusP002BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP002Center2558‖ ≤ batchN02703MinusP002Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP002Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP002Input2558]
  have hs : compactExp2547 batchN02703MinusP002Input2558 8 =
      (batchN02703MinusP002Center2558, ((13890051478555904937 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP002Input2558 8).2 : ℝ) =
      batchN02703MinusP002Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP002Error2558]
  have h := compactExp_error2547 batchN02703MinusP002Input2558 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchN02703MinusP002Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP002Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP002DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨2, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP002Factor2558 * embedPair2542 batchN02703MinusP002Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP002Factor2558 : ℝ) * batchN02703MinusP002Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP002Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP002Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP002BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP002Factor2558)

def batchN02703MinusP003Input2558 : RatPair2542 := ((((-((1123650 * 10^40
        + 2960581386159307605172018669347586747959) * 10^40
        + 6646801809483559253159682348452673876229)) : ℚ) /
        ((6650196 * 10^40
        + 4642788052740272456750226203440576329812) * 10^40
        + 5806699242230935752901173261107200000000)),
    (((-875050540262952370391324093) : ℚ) /
        1844674407370955161600000000))

def batchN02703MinusP003Center2558 : RatPair2542 := ((((-111959054128113850382852145511) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-52941125960634317898434698617) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN02703MinusP003Factor2558 : RatPair2542 :=
    ((((-(((((((((((175814191728953908120477513237618313
    *
    10^40
        + 4532208406473268853591446940467114942834) * 10^40
        + 2617811683210076036313781132761087056248) * 10^40
        + 6044507837903087984444779364700007830305) * 10^40
        + 5385058189949731000111001815383430620743) * 10^40
        + 5527947573120280999818527659434907951307) * 10^40
        + 2095749679616864519557426770531636573275) * 10^40
        + 1479963013342975753194737816466847276204) * 10^40
        + 9654276279194104507965845063823383811978) * 10^40
        + 7057360635868647098211877074922893234785) * 10^40
        + 3118737540815180524749392528091407003784) * 10^40
        + 4036311365629959497471709927915931199839)) : ℚ) /
        (((((((((((2850891405191799806493662203013 * 10^40
        + 2866175188564300898013286549645205272239) * 10^40
        + 4236694705205800815518432960890697473092) * 10^40
        + 231035487920911788918903827658063106460) * 10^40
        + 7135239681676367284304118298194798451497) * 10^40
        + 9230241821743401790116435944769808335534) * 10^40
        + 7118113905748534593652612413141568410716) * 10^40
        + 7551390266786915241413554700256585070979) * 10^40
        + 4932678937114678692019809518378414404839) * 10^40
        + 4691433886864041236488066618953759608310) * 10^40
        + 1231904796717969731765037025078423457515) * 10^40
        + 3362812955343920090843605091542603137024)),
    (((-((((((((1375126096647683408346 * 10^40
        + 1995131699139155794900371370554137416948) * 10^40
        + 6301194974674023721529276679578341692534) * 10^40
        + 821365449726841872294628809593127318711) * 10^40
        + 5015576184570965541286239146467712841913) * 10^40
        + 1214914255641543516729047197586768731856) * 10^40
        + 2645108795446351583492978606233862106586) * 10^40
        + 2990125938248544468944088350443681337695) * 10^40
        + 2327329459042770333486334918807369785871)) : ℚ) /
        ((((((((34636089907672889 * 10^40
        + 3876307236658840489794075718006094752826) * 10^40
        + 203810856020369271949540357259607569633) * 10^40
        + 9302324058009588998586262310298447064443) * 10^40
        + 9775213280141220902088527666684960977896) * 10^40
        + 3907076410628223875185174683413135137386) * 10^40
        + 5319613430253880313421172981150036075516) * 10^40
        + 572554727302983815773468199960404814194) * 10^40
        + 2635661122408427397415491815225914556416)))

noncomputable def batchN02703MinusP003Error2558 : ℝ := ((836402606886840621453327411 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP003BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP003Center2558‖ ≤ batchN02703MinusP003Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP003Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP003Input2558]
  have hs : compactExp2547 batchN02703MinusP003Input2558 8 =
      (batchN02703MinusP003Center2558, ((836402606886840621453327411 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP003Input2558 8).2 : ℝ) =
      batchN02703MinusP003Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP003Error2558]
  have h := compactExp_error2547 batchN02703MinusP003Input2558 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchN02703MinusP003Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP003Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP003DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨3, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP003Factor2558 * embedPair2542 batchN02703MinusP003Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP003Factor2558 : ℝ) * batchN02703MinusP003Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP003Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP003Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP003BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP003Factor2558)

def batchN02703MinusP004Input2558 : RatPair2542 := ((((-((19409 * 10^40
        + 7076422721502121743027980817409819781999) * 10^40
        + 486238254540120343256631437462245422927)) : ℚ) /
        ((134092 * 10^40
        + 2376048615170942017213126254407586180041) * 10^40
        + 6181592905822546762729310624153600000000)),
    ((875050540262952370391324093 : ℚ) /
        1844674407370955161600000000))

def batchN02703MinusP004Center2558 : RatPair2542 := ((((-55129591407190581895480487846843) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((26068661133083737741581242579421 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchN02703MinusP004Factor2558 : RatPair2542 := ((((-(((((((((((216904835924513972037703 *
    10^40
        + 5528023141277441421230596180402280388089) * 10^40
        + 3591828663982531151231018663048920955214) * 10^40
        + 1798562506446466192152017180180648871899) * 10^40
        + 8506777594505291541874188735248249752073) * 10^40
        + 5308104168679856502247988164450228079808) * 10^40
        + 4763011321307498543702012079203067033082) * 10^40
        + 9914189714747236804957060557974183384363) * 10^40
        + 5243618720925644503379661304099015596449) * 10^40
        + 9163203937444018755589311526870974511039) * 10^40
        + 5754499989355969664060080826629196372326) * 10^40
        + 9935926341815767516753465180617692059013)) : ℚ) /
        (((((((((((7096298639243998729 * 10^40
        + 4403841801617833293488489545355147756991) * 10^40
        + 6565153813449888842034323198064457918567) * 10^40
        + 9656840824907094861052821676383945831815) * 10^40
        + 4655880462233727603219253377645202181115) * 10^40
        + 8409568548945938213507895737537587135979) * 10^40
        + 8969051343206717833204665933243475350959) * 10^40
        + 9611428944588179000071332720910212643642) * 10^40
        + 5180853756333196021319972889124751437975) * 10^40
        + 734462828462439992991999015744320026649) * 10^40
        + 3449159869212450393966926771217058623019) * 10^40
        + 6472631504120681589459448663002377617408)),
    ((((((((((106580736696511 * 10^40
        + 8327226834924484487548071150286941530627) * 10^40
        + 7134085271840446276899023319569309777033) * 10^40
        + 4920053842539380761859797014174082091168) * 10^40
        + 3672351589906311933386363700425174074305) * 10^40
        + 4951074792186620073866694444551806370959) * 10^40
        + 300473182680970532187108939675549946510) * 10^40
        + 6956122385545143253179582946472582591057) * 10^40
        + 3495709729592302648058167397784819286677) : ℚ) /
        ((((((((1908465232 * 10^40
        + 3293027429626111139973596082439847932115) * 10^40
        + 6664321391713498099047180941162754673840) * 10^40
        + 6954451384019147938886101576492143057143) * 10^40
        + 5540725407879060131012381893497590623294) * 10^40
        + 701844789492284305595216490777219573839) * 10^40
        + 9592297085941490583006275557464927696997) * 10^40
        + 4452147618892087849389831123500845390904) * 10^40
        + 960634030571069208048182463329145454592)))

noncomputable def batchN02703MinusP004Error2558 : ℝ := ((401998131106820665747522716369 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP004BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP004Center2558‖ ≤ batchN02703MinusP004Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP004Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP004Input2558]
  have hs : compactExp2547 batchN02703MinusP004Input2558 8 =
      (batchN02703MinusP004Center2558, ((401998131106820665747522716369 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP004Input2558 8).2 : ℝ) =
      batchN02703MinusP004Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP004Error2558]
  have h := compactExp_error2547 batchN02703MinusP004Input2558 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchN02703MinusP004Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP004Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP004DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨4, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP004Factor2558 * embedPair2542 batchN02703MinusP004Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP004Factor2558 : ℝ) * batchN02703MinusP004Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP004Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP004Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP004BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP004Factor2558)

def batchN02703MinusP005Center2558 : RatPair2542 := (0, 0)

def batchN02703MinusP005Factor2558 : RatPair2542 := (0, 0)

noncomputable def batchN02703MinusP005Error2558 : ℝ := 0

theorem batchN02703MinusP005Exterior2558 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02703MinusPosition2558 = 0
        := by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |batchN02703MinusPosition2558| := by
    norm_num [storedWidth, batchN02703MinusPosition2558]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem batchN02703MinusP005BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP005Center2558‖ ≤ batchN02703MinusP005Error2558 := by
  rw [batchN02703MinusP005Exterior2558]
  norm_num [batchN02703MinusP005Center2558, batchN02703MinusP005Error2558,
      batchN02703MinusZero2558]

theorem batchN02703MinusP005DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨5, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP005Factor2558 * embedPair2542 batchN02703MinusP005Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP005Factor2558 : ℝ) * batchN02703MinusP005Error2558 :=
            by
  rw [batchN02703MinusP005Exterior2558]
  norm_num [batchN02703MinusP005Factor2558, batchN02703MinusP005Center2558,
      batchN02703MinusP005Error2558,
      batchN02703MinusZero2558, pairMagnitude2542]

def batchN02703MinusP006Input2558 : RatPair2542 := ((((-42059867730981584248264924735116571) : ℚ)
    /
        73628896602487849615844966400000000),
    ((0 : ℚ) /
        1))

def batchN02703MinusP006Center2558 : RatPair2542 := (((25684408913017653 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchN02703MinusP006Factor2558 : RatPair2542 := ((((((2235699584886981722 * 10^40
        + 190008361994198605501465797104653283694) * 10^40
        + 809316130585987907153053443679481576062) * 10^40
        + 3445401292401414008544547414269723686957) : ℚ) /
        (((6787095290940 * 10^40
        + 7008289208078989014891901531081169084460) * 10^40
        + 8061032457859395500337340527383380851568) * 10^40
        + 4705628572133327931643620685842210504344)),
    ((0 : ℚ) /
        1))

noncomputable def batchN02703MinusP006Error2558 : ℝ := ((4299411043621 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchN02703MinusP006BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP006Center2558‖ ≤ batchN02703MinusP006Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP006Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP006Input2558]
  have hs : compactExp2547 batchN02703MinusP006Input2558 7 =
      (batchN02703MinusP006Center2558, ((4299411043621 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP006Input2558 7).2 : ℝ) =
      batchN02703MinusP006Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP006Error2558]
  have h := compactExp_error2547 batchN02703MinusP006Input2558 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          batchN02703MinusP006Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP006Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP006DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨6, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP006Factor2558 * embedPair2542 batchN02703MinusP006Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP006Factor2558 : ℝ) * batchN02703MinusP006Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP006Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP006Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP006BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP006Factor2558)

def batchN02703MinusP007Input2558 : RatPair2542 := ((((-((1123650 * 10^40
        + 2960581386159307605172018669347586747959) * 10^40
        + 6646801809483559253159682348452673876229)) : ℚ) /
        ((1662549 * 10^40
        + 1160697013185068114187556550860144082453) * 10^40
        + 1451674810557733938225293315276800000000)),
    ((0 : ℚ) /
        1))

def batchN02703MinusP007Center2558 : RatPair2542 := (((29942401709609983149248847675 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1))

def batchN02703MinusP007Factor2558 : RatPair2542 := ((((((((((((((1192792 * 10^40
        + 8853327104139905709960137885828259583049) * 10^40
        + 980238972690811609873750127816226077520) * 10^40
        + 2562913576610413093216440568513134387340) * 10^40
        + 4547445047749744518450111969888723893799) * 10^40
        + 348733330529297072799162892006702347525) * 10^40
        + 816134475086526548655454119880655762513) * 10^40
        + 8647299566895412715647812864114624144849) * 10^40
        + 4936766296467629654130268707816611547583) * 10^40
        + 4385664523483685679857163196766657167989) * 10^40
        + 5991517203248153730436671055237816977217) * 10^40
        + 7660817792852168295627293588394692421357) : ℚ) /
        (((((((((((575 * 10^40
        + 7329342941198209084504874756649288820246) * 10^40
        + 199441750951135344688525648150343858022) * 10^40
        + 8636868457821536928262927077391427903787) * 10^40
        + 5881081889967584734016501827254014117325) * 10^40
        + 9256671068389817549145823114162212953339) * 10^40
        + 4829990601628655361798203710705999776155) * 10^40
        + 3857802538834450453945713897881802193266) * 10^40
        + 9909663258441527763452626573679229610064) * 10^40
        + 8308620985007516490171485110995107611476) * 10^40
        + 7024745600620798456360047956068718236593) * 10^40
        + 3118321657182653634981651292842460629144)),
    ((0 : ℚ) /
        1))

noncomputable def batchN02703MinusP007Error2558 : ℝ := ((8283591204048782430816091 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchN02703MinusP007BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP007Center2558‖ ≤ batchN02703MinusP007Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP007Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP007Input2558]
  have hs : compactExp2547 batchN02703MinusP007Input2558 6 =
      (batchN02703MinusP007Center2558, ((8283591204048782430816091 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP007Input2558 6).2 : ℝ) =
      batchN02703MinusP007Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP007Error2558]
  have h := compactExp_error2547 batchN02703MinusP007Input2558 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          batchN02703MinusP007Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP007Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP007DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨7, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP007Factor2558 * embedPair2542 batchN02703MinusP007Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP007Factor2558 : ℝ) * batchN02703MinusP007Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP007Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP007Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP007BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP007Factor2558)

def batchN02703MinusP008Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((630207761169656792930558849 : ℚ) /
        236118324143482260684800000000))

def batchN02703MinusP008Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP008Factor2558 : RatPair2542 :=
    ((((((((((((((1208456373623697945978222928734494 *
    10^40
        + 3101474194408087624684875308348343471188) * 10^40
        + 5233972944107471470652781197874742598194) * 10^40
        + 2134507564222476846990046231672204482933) * 10^40
        + 3772387357812061681082014475749737357625) * 10^40
        + 3056741062689025786243287767853224546257) * 10^40
        + 4467937287076557094251534010320161113082) * 10^40
        + 3462859395758209102336643095075663950076) * 10^40
        + 7276760880271019216776152834312218398516) * 10^40
        + 8597248847318471817545946458360490874538) * 10^40
        + 2589304185078830808080367323932300603972) * 10^40
        + 7111545212416309587480548909901711398649) : ℚ) /
        (((((((((((38641377360981 * 10^40
        + 8873852151373369757829717128200782685752) * 10^40
        + 4267057942768750294902133717342921669223) * 10^40
        + 9399605917700734948399086841320199281338) * 10^40
        + 4859539904081381412894660520764426547703) * 10^40
        + 82382791360191671191032808584389846206) * 10^40
        + 1633019325131816678569845070580499075466) * 10^40
        + 3956836426740748781909118217643538577729) * 10^40
        + 6267509885714671841731005978953973770642) * 10^40
        + 359241977727099007846112302491997327807) * 10^40
        + 921697033459657461089294888561088334141) * 10^40
        + 716934100152927431698260366170412548096)),
    (((-((((((((263163796312357604048 * 10^40
        + 2076572268186985909679142256266300873390) * 10^40
        + 3124590844186862613784474068333257920250) * 10^40
        + 3506229679248910563169995108708350049253) * 10^40
        + 6869736850593285194419962033756015388447) * 10^40
        + 1434735366007569373335640487676301179467) * 10^40
        + 6691707451138727665884617714342975628906) * 10^40
        + 8649800192981746715452571824381852473080) * 10^40
        + 4261482100651591209325534041856996715293)) : ℚ) /
        ((((((((625115 * 10^40
        + 3070591823028432807900138902629006870138) * 10^40
        + 9213498945994495547896095054549184966732) * 10^40
        + 8226484035244854201144520710067684189290) * 10^40
        + 7139261586645251409515326151884038850512) * 10^40
        + 6496911643360556854668003275362206146245) * 10^40
        + 2646206673659696455168439317147406759979) * 10^40
        + 66561741935084967797981034531203650932) * 10^40
        + 4083820426170737774826014521807316451328)))

noncomputable def batchN02703MinusP008Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP008BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP008Center2558‖ ≤ batchN02703MinusP008Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP008Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP008Input2558]
  have hs : compactExp2547 batchN02703MinusP008Input2558 14 =
      (batchN02703MinusP008Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP008Input2558 14).2 : ℝ) =
      batchN02703MinusP008Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP008Error2558]
  have h := compactExp_error2547 batchN02703MinusP008Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP008Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP008Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP008DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨8, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP008Factor2558 * embedPair2542 batchN02703MinusP008Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP008Factor2558 : ℝ) * batchN02703MinusP008Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP008Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP008Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP008BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP008Factor2558)

def batchN02703MinusP009Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((937284057746035612622411487 : ℚ) /
        236118324143482260684800000000))

def batchN02703MinusP009Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP009Factor2558 : RatPair2542 :=
    ((((((((((((((1208456373535248063722418740112667 *
    10^40
        + 7468664860288566618946283932975996334662) * 10^40
        + 3731039282050522636841881506634412398516) * 10^40
        + 5283284210611508562823918229446908269691) * 10^40
        + 8251253346543628375897183156899329058839) * 10^40
        + 1434163864621311004532639778771022946431) * 10^40
        + 894802942030575396846539578873395359870) * 10^40
        + 145380731537337687323406306039692167134) * 10^40
        + 3242177933775110041697773609368893291476) * 10^40
        + 4893593751779009069575927285770305948924) * 10^40
        + 5631005774339724150971482437432984020422) * 10^40
        + 2514998724262670928788965205392508349497) : ℚ) /
        (((((((((((38641377360981 * 10^40
        + 8873852151373369757829717128200782685752) * 10^40
        + 4267057942768750294902133717342921669223) * 10^40
        + 9399605917700734948399086841320199281338) * 10^40
        + 4859539904081381412894660520764426547703) * 10^40
        + 82382791360191671191032808584389846206) * 10^40
        + 1633019325131816678569845070580499075466) * 10^40
        + 3956836426740748781909118217643538577729) * 10^40
        + 6267509885714671841731005978953973770642) * 10^40
        + 359241977727099007846112302491997327807) * 10^40
        + 921697033459657461089294888561088334141) * 10^40
        + 716934100152927431698260366170412548096)),
    (((-((((((((130464505017465120338 * 10^40
        + 6170554079917310195443285345104009103303) * 10^40
        + 3527608829285394592196606679533459932161) * 10^40
        + 1974201944354666702046183989990394794246) * 10^40
        + 85626032035727170077333255823198531309) * 10^40
        + 5362023966338197508200987820144292600062) * 10^40
        + 9668406781008080543223709260262811224670) * 10^40
        + 7285921507680029279457287526754140228481) * 10^40
        + 1752135105932209323392198426902071593601)) : ℚ) /
        ((((((((208371 * 10^40
        + 7690197274342810935966712967543002290046) * 10^40
        + 3071166315331498515965365018183061655577) * 10^40
        + 6075494678414951400381506903355894729763) * 10^40
        + 5713087195548417136505108717294679616837) * 10^40
        + 5498970547786852284889334425120735382081) * 10^40
        + 7548735557886565485056146439049135586659) * 10^40
        + 6688853913978361655932660344843734550310) * 10^40
        + 8027940142056912591608671507269105483776)))

noncomputable def batchN02703MinusP009Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP009BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP009Center2558‖ ≤ batchN02703MinusP009Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP009Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP009Input2558]
  have hs : compactExp2547 batchN02703MinusP009Input2558 14 =
      (batchN02703MinusP009Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP009Input2558 14).2 : ℝ) =
      batchN02703MinusP009Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP009Error2558]
  have h := compactExp_error2547 batchN02703MinusP009Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP009Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP009Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP009DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨9, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP009Factor2558 * embedPair2542 batchN02703MinusP009Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP009Factor2558 : ℝ) * batchN02703MinusP009Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP009Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP009Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP009BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP009Factor2558)

def batchN02703MinusP010Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((557564310676873452549325257 : ℚ) /
        118059162071741130342400000000))

def batchN02703MinusP010Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP010Factor2558 : RatPair2542 :=
    ((((((((((((((302114093367043641086635526891565 *
    10^40
        + 4213715614427151589661696819804152426602) * 10^40
        + 4951382542988887321745415703482841843149) * 10^40
        + 5358979216516668449225697869959275769279) * 10^40
        + 3283285822547766661344723945363629958756) * 10^40
        + 5854998668412401870347704387335685398505) * 10^40
        + 4073689686897015201600372086540073340830) * 10^40
        + 7597015017558112274920291248530091635394) * 10^40
        + 6069002656296542532552955433876020454255) * 10^40
        + 9485128352624324462716937667618427593590) * 10^40
        + 9608504099279335810095217996939917779533) * 10^40
        + 2630551611334419091905574098648646367561) : ℚ) /
        (((((((((((9660344340245 * 10^40
        + 4718463037843342439457429282050195671438) * 10^40
        + 1066764485692187573725533429335730417305) * 10^40
        + 9849901479425183737099771710330049820334) * 10^40
        + 6214884976020345353223665130191106636925) * 10^40
        + 7520595697840047917797758202146097461551) * 10^40
        + 5408254831282954169642461267645124768866) * 10^40
        + 5989209106685187195477279554410884644432) * 10^40
        + 4066877471428667960432751494738493442660) * 10^40
        + 5089810494431774751961528075622999331951) * 10^40
        + 7730424258364914365272323722140272083535) * 10^40
        + 2679233525038231857924565091542603137024)),
    (((-((((((((2155825511850090739 * 10^40
        + 1917626645167921378760068115262671295578) * 10^40
        + 5296915609836753065608292344963209425023) * 10^40
        + 950751294144503702789366613303053439306) * 10^40
        + 4577452980023411734994661188910328094139) * 10^40
        + 2433972862488510258245461803917898613486) * 10^40
        + 3582486619889820513873659763062617329248) * 10^40
        + 2195099669393930146978165464858406795174) * 10^40
        + 2208167980478612510896578762245392435023)) : ℚ) /
        ((((((((2894 * 10^40
        + 523474962143650151888426568993652809583) * 10^40
        + 9764877309935159701610630069696986967438) * 10^40
        + 5778826314977985436116409818102165204580) * 10^40
        + 496015099938172460229237621073537216900) * 10^40
        + 5215263479830372948401240755904454658084) * 10^40
        + 4688176882748424520625779811653460216481) * 10^40
        + 3842900748805255022999064727011718535420) * 10^40
        + 9833721390861901563772342659823182020608)))

noncomputable def batchN02703MinusP010Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP010BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP010Center2558‖ ≤ batchN02703MinusP010Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP010Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP010Input2558]
  have hs : compactExp2547 batchN02703MinusP010Input2558 14 =
      (batchN02703MinusP010Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP010Input2558 14).2 : ℝ) =
      batchN02703MinusP010Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP010Error2558]
  have h := compactExp_error2547 batchN02703MinusP010Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP010Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP010Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP010DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨10, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP010Factor2558 * embedPair2542 batchN02703MinusP010Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP010Factor2558 : ℝ) * batchN02703MinusP010Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP010Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP010Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP010BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP010Factor2558)

def batchN02703MinusP011Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((616851458366379977328285017 : ℚ) /
        118059162071741130342400000000))

def batchN02703MinusP011Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP011Factor2558 : RatPair2542 :=
    ((((((((((((((302114093354248999845676902526692 *
    10^40
        + 5648024800555332645939665321952424673799) * 10^40
        + 7904654765461030516332526316845015107211) * 10^40
        + 2004766521794689152991972252613194795381) * 10^40
        + 5993372111831249637143594542824631219977) * 10^40
        + 2910077065652045388003552274082593526072) * 10^40
        + 258343257305481084031888011383442583663) * 10^40
        + 1194772700790709988440865237791627407188) * 10^40
        + 6911165920734839606100446561481582672502) * 10^40
        + 2433642082068266245447383357981102060625) * 10^40
        + 4754702160896801900511452697082239040876) * 10^40
        + 5507677558479386040970966344628177828201) : ℚ) /
        (((((((((((9660344340245 * 10^40
        + 4718463037843342439457429282050195671438) * 10^40
        + 1066764485692187573725533429335730417305) * 10^40
        + 9849901479425183737099771710330049820334) * 10^40
        + 6214884976020345353223665130191106636925) * 10^40
        + 7520595697840047917797758202146097461551) * 10^40
        + 5408254831282954169642461267645124768866) * 10^40
        + 5989209106685187195477279554410884644432) * 10^40
        + 4066877471428667960432751494738493442660) * 10^40
        + 5089810494431774751961528075622999331951) * 10^40
        + 7730424258364914365272323722140272083535) * 10^40
        + 2679233525038231857924565091542603137024)),
    (((-((((((((64396609159548785481 * 10^40
        + 4531389262314162619336995903925257574948) * 10^40
        + 1541785554488728280257304423409496515220) * 10^40
        + 3915964043836539934753907329844208145444) * 10^40
        + 9524504296948274735913940726252054169130) * 10^40
        + 5615406105465964738607098278298046328842) * 10^40
        + 5953042272917724749904628016665304406581) * 10^40
        + 7866170756357474384865624484379404880092) * 10^40
        + 833630668589708841382746130530535863621)) : ℚ) /
        ((((((((78139 * 10^40
        + 4133823977878554100987517362828625858767) * 10^40
        + 3651687368249311943487011881818648120841) * 10^40
        + 6028310504405606775143065088758460523661) * 10^40
        + 3392407698330656426189415768985504856314) * 10^40
        + 812113955420069606833500409420275768280) * 10^40
        + 6580775834207462056896054914643425844997) * 10^40
        + 3758320217741885620974747629316400456366) * 10^40
        + 5510477553271342221853251815225914556416)))

noncomputable def batchN02703MinusP011Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP011BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP011Center2558‖ ≤ batchN02703MinusP011Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP011Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP011Input2558]
  have hs : compactExp2547 batchN02703MinusP011Input2558 14 =
      (batchN02703MinusP011Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP011Input2558 14).2 : ℝ) =
      batchN02703MinusP011Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP011Error2558]
  have h := compactExp_error2547 batchN02703MinusP011Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP011Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP011Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP011DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨11, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP011Factor2558 * embedPair2542 batchN02703MinusP011Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP011Factor2558 : ℝ) * batchN02703MinusP011Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP011Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP011Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP011BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP011Factor2558)

def batchN02703MinusP012Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((13565168671393720424251253 : ℚ) /
        2361183241434822606848000000))

def batchN02703MinusP012Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP012Factor2558 : RatPair2542 := ((((((((((((((75528523334908742349303188964694
    *
    10^40
        + 1503457452232193252388262939113762110297) * 10^40
        + 5566249701859557741087675700113126605160) * 10^40
        + 5348632540696430551521038126774022593933) * 10^40
        + 5864946792832385612926914275653426421043) * 10^40
        + 6743617354037801908819579576911620688642) * 10^40
        + 5042352458934086858063855371472623120990) * 10^40
        + 6784449610629590837681605780467312115077) * 10^40
        + 9620494193240387378966373466976500280847) * 10^40
        + 4280722256548901472016354256335125676848) * 10^40
        + 6821229744891484552526485311766440079322) * 10^40
        + 9755646754174377919407114252184155682593) : ℚ) /
        (((((((((((2415086085061 * 10^40
        + 3679615759460835609864357320512548917859) * 10^40
        + 5266691121423046893431383357333932604326) * 10^40
        + 4962475369856295934274942927582512455083) * 10^40
        + 6553721244005086338305916282547776659231) * 10^40
        + 4380148924460011979449439550536524365387) * 10^40
        + 8852063707820738542410615316911281192216) * 10^40
        + 6497302276671296798869319888602721161108) * 10^40
        + 1016719367857166990108187873684623360665) * 10^40
        + 1272452623607943687990382018905749832987) * 10^40
        + 9432606064591228591318080930535068020883) * 10^40
        + 8169808381259557964481141272885650784256)),
    (((-((((((((8850903783868868138 * 10^40
        + 9316500571790696753215528728250087333519) * 10^40
        + 8888284718130035754585764051193754625672) * 10^40
        + 14227082230204814601707764529379084752) * 10^40
        + 4847197330740453590319907380167669467903) * 10^40
        + 6760224108223328691292674552717641319333) * 10^40
        + 1648836383980868099330365765732753412708) * 10^40
        + 8201157230083895863781940033486336161421) * 10^40
        + 4534345071527344033566681998528790100225)) : ℚ) /
        ((((((((9767 * 10^40
        + 4266727997234819262623439670353578232345) * 10^40
        + 9206460921031163992935876485227331015105) * 10^40
        + 2003538813050700846892883136094807565457) * 10^40
        + 6674050962291332053273676971123188107039) * 10^40
        + 2601514244427508700854187551177534471035) * 10^40
        + 822596979275932757112006864330428230624) * 10^40
        + 6719790027217735702621843453664550057045) * 10^40
        + 8188809694158917777731656476903239319552)))

noncomputable def batchN02703MinusP012Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP012BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP012Center2558‖ ≤ batchN02703MinusP012Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP012Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP012Input2558]
  have hs : compactExp2547 batchN02703MinusP012Input2558 14 =
      (batchN02703MinusP012Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP012Input2558 14).2 : ℝ) =
      batchN02703MinusP012Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP012Error2558]
  have h := compactExp_error2547 batchN02703MinusP012Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP012Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP012Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP012DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨12, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP012Factor2558 * embedPair2542 batchN02703MinusP012Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP012Factor2558 : ℝ) * batchN02703MinusP012Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP012Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP012Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP012BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP012Factor2558)

def batchN02703MinusP013Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((146843544667941034181224347 : ℚ) /
        23611832414348226068480000000))

def batchN02703MinusP013Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP013Factor2558 : RatPair2542 :=
    ((((((((((((((302114093325110542623778442357256 *
    10^40
        + 6425298601036410608962955925344654576545) * 10^40
        + 7412595409239291490909971174087487218514) * 10^40
        + 1621639091981052396646304220504966855676) * 10^40
        + 7785049953502447641905750373219984942160) * 10^40
        + 5072464736490840726790063069742255388070) * 10^40
        + 1348442771540183081608991751379917405096) * 10^40
        + 5898599472568611626858315474813144995299) * 10^40
        + 8935626616806765414729265005951044302138) * 10^40
        + 6304202632541693827375035894108335487520) * 10^40
        + 2535230300848913434982164428031001829504) * 10^40
        + 315874476904932193071618344015804349097) : ℚ) /
        (((((((((((9660344340245 * 10^40
        + 4718463037843342439457429282050195671438) * 10^40
        + 1066764485692187573725533429335730417305) * 10^40
        + 9849901479425183737099771710330049820334) * 10^40
        + 6214884976020345353223665130191106636925) * 10^40
        + 7520595697840047917797758202146097461551) * 10^40
        + 5408254831282954169642461267645124768866) * 10^40
        + 5989209106685187195477279554410884644432) * 10^40
        + 4066877471428667960432751494738493442660) * 10^40
        + 5089810494431774751961528075622999331951) * 10^40
        + 7730424258364914365272323722140272083535) * 10^40
        + 2679233525038231857924565091542603137024)),
    (((-((((((((25549712239545080387 * 10^40
        + 7218276708271773315030998034567028272658) * 10^40
        + 5058896311242474507954238950631745642174) * 10^40
        + 6365341214195191035049976873814925294315) * 10^40
        + 9486726010321274929590145830143311484080) * 10^40
        + 4842369192454006820049561163510616570102) * 10^40
        + 7234779554303740019129863166701131457602) * 10^40
        + 9163569964931955284261421229309875305475) * 10^40
        + 3231956848012151089968899264918414373065)) : ℚ) /
        ((((((((26046 * 10^40
        + 4711274659292851366995839120942875286255) * 10^40
        + 7883895789416437314495670627272882706947) * 10^40
        + 2009436834801868925047688362919486841220) * 10^40
        + 4464135899443552142063138589661834952104) * 10^40
        + 6937371318473356535611166803140091922760) * 10^40
        + 2193591944735820685632018304881141948332) * 10^40
        + 4586106739247295206991582543105466818788) * 10^40
        + 8503492517757114073951083938408638185472)))

noncomputable def batchN02703MinusP013Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP013BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP013Center2558‖ ≤ batchN02703MinusP013Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP013Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP013Input2558]
  have hs : compactExp2547 batchN02703MinusP013Input2558 14 =
      (batchN02703MinusP013Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP013Input2558 14).2 : ℝ) =
      batchN02703MinusP013Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP013Error2558]
  have h := compactExp_error2547 batchN02703MinusP013Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP013Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP013Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP013DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨13, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP013Factor2558 * embedPair2542 batchN02703MinusP013Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP013Factor2558 : ℝ) * batchN02703MinusP013Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP013Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP013Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP013BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP013Factor2558)

def batchN02703MinusP014Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((837904556009299227857391587 : ℚ) /
        118059162071741130342400000000))

def batchN02703MinusP014Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP014Factor2558 : RatPair2542 :=
    ((((((((((((((302114093295156488330899201287562 *
    10^40
        + 5897049960906110219784729776303905806781) * 10^40
        + 5941210814481374121876745559712651100923) * 10^40
        + 5977889042972166349840784643422200397407) * 10^40
        + 5357564717013795310098598478070525094323) * 10^40
        + 6486623211462166031592725866283987908830) * 10^40
        + 7542602619865421237082219801134026542608) * 10^40
        + 6364866125255062883599773585072870853446) * 10^40
        + 4707834488712419788309863985888122063794) * 10^40
        + 5599521993198327880400096131979440649367) * 10^40
        + 25934937794785125889022570318437342934) * 10^40
        + 5436479275524507340284440216544722817281) : ℚ) /
        (((((((((((9660344340245 * 10^40
        + 4718463037843342439457429282050195671438) * 10^40
        + 1066764485692187573725533429335730417305) * 10^40
        + 9849901479425183737099771710330049820334) * 10^40
        + 6214884976020345353223665130191106636925) * 10^40
        + 7520595697840047917797758202146097461551) * 10^40
        + 5408254831282954169642461267645124768866) * 10^40
        + 5989209106685187195477279554410884644432) * 10^40
        + 4066877471428667960432751494738493442660) * 10^40
        + 5089810494431774751961528075622999331951) * 10^40
        + 7730424258364914365272323722140272083535) * 10^40
        + 2679233525038231857924565091542603137024)),
    (((-((((((((87473591045828800657 * 10^40
        + 178091796905998328690480053564243184352) * 10^40
        + 273946066932592935786505182833694174021) * 10^40
        + 4582542175044878921908325216231727376344) * 10^40
        + 191396087009934396803614905231686749258) * 10^40
        + 440063379384135819271215355495242225658) * 10^40
        + 6717937334113166940633354034895882044486) * 10^40
        + 8417274005538238539541378118131966773832) * 10^40
        + 4307021755283792867036837264862086660271)) : ℚ) /
        ((((((((78139 * 10^40
        + 4133823977878554100987517362828625858767) * 10^40
        + 3651687368249311943487011881818648120841) * 10^40
        + 6028310504405606775143065088758460523661) * 10^40
        + 3392407698330656426189415768985504856314) * 10^40
        + 812113955420069606833500409420275768280) * 10^40
        + 6580775834207462056896054914643425844997) * 10^40
        + 3758320217741885620974747629316400456366) * 10^40
        + 5510477553271342221853251815225914556416)))

noncomputable def batchN02703MinusP014Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP014BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP014Center2558‖ ≤ batchN02703MinusP014Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP014Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP014Input2558]
  have hs : compactExp2547 batchN02703MinusP014Input2558 14 =
      (batchN02703MinusP014Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP014Input2558 14).2 : ℝ) =
      batchN02703MinusP014Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP014Error2558]
  have h := compactExp_error2547 batchN02703MinusP014Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP014Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP014Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP014DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨14, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP014Factor2558 * embedPair2542 batchN02703MinusP014Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP014Factor2558 : ℝ) * batchN02703MinusP014Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP014Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP014Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP014BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP014Factor2558)

def batchN02703MinusP015Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((912196524516605512925256599 : ℚ) /
        118059162071741130342400000000))

def batchN02703MinusP015Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP015Factor2558 : RatPair2542 :=
    ((((((((((((((302114093271264588738032322279894 *
    10^40
        + 9312071505503578337756036487104862146875) * 10^40
        + 2190910422420878798834424895959491236036) * 10^40
        + 9013140077050442692926082029672604002559) * 10^40
        + 800549149783837207319277051247182721446) * 10^40
        + 555350845314774975368524515795625721799) * 10^40
        + 1635601085878200610764834948667347269908) * 10^40
        + 9528540732281286284918614779794755962556) * 10^40
        + 7356106568305520472044944776762977975438) * 10^40
        + 6852546103859988331299895325591734307628) * 10^40
        + 5571562543500907865641686419927300177358) * 10^40
        + 2070924692572431633830777959415659537033) : ℚ) /
        (((((((((((9660344340245 * 10^40
        + 4718463037843342439457429282050195671438) * 10^40
        + 1066764485692187573725533429335730417305) * 10^40
        + 9849901479425183737099771710330049820334) * 10^40
        + 6214884976020345353223665130191106636925) * 10^40
        + 7520595697840047917797758202146097461551) * 10^40
        + 5408254831282954169642461267645124768866) * 10^40
        + 5989209106685187195477279554410884644432) * 10^40
        + 4066877471428667960432751494738493442660) * 10^40
        + 5089810494431774751961528075622999331951) * 10^40
        + 7730424258364914365272323722140272083535) * 10^40
        + 2679233525038231857924565091542603137024)),
    (((-((((((((95229349412208509259 * 10^40
        + 6453809451551104189744632474883711435244) * 10^40
        + 489442103841819832344261525236743210877) * 10^40
        + 9271155144001514818412181477621354122729) * 10^40
        + 4084998818223553889420344331762129363007) * 10^40
        + 6635086918113289375131673719254055582549) * 10^40
        + 3402497737507865288248896077910864130711) * 10^40
        + 2811620218009076321034696627693710297455) * 10^40
        + 9550518262764828438876673547095222139979)) : ℚ) /
        ((((((((78139 * 10^40
        + 4133823977878554100987517362828625858767) * 10^40
        + 3651687368249311943487011881818648120841) * 10^40
        + 6028310504405606775143065088758460523661) * 10^40
        + 3392407698330656426189415768985504856314) * 10^40
        + 812113955420069606833500409420275768280) * 10^40
        + 6580775834207462056896054914643425844997) * 10^40
        + 3758320217741885620974747629316400456366) * 10^40
        + 5510477553271342221853251815225914556416)))

noncomputable def batchN02703MinusP015Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP015BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP015Center2558‖ ≤ batchN02703MinusP015Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP015Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP015Input2558]
  have hs : compactExp2547 batchN02703MinusP015Input2558 14 =
      (batchN02703MinusP015Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP015Input2558 14).2 : ℝ) =
      batchN02703MinusP015Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP015Error2558]
  have h := compactExp_error2547 batchN02703MinusP015Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP015Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP015Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP015DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨15, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP015Factor2558 * embedPair2542 batchN02703MinusP015Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP015Factor2558 : ℝ) * batchN02703MinusP015Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP015Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP015Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP015BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP015Factor2558)

def batchN02703MinusP016Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((482942851321834514582086953 : ℚ) /
        59029581035870565171200000000))

def batchN02703MinusP016Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP016Factor2558 : RatPair2542 := ((((((((((((((75528523313183949881339402944309
    *
    10^40
        + 1990708563552832683688700018615365964265) * 10^40
        + 4066395661703126759625433644340746755121) * 10^40
        + 6753329099713291168066867923582298602367) * 10^40
        + 7393263979667292622166037373341045633027) * 10^40
        + 7733796246740222628998668528423658530366) * 10^40
        + 3652858429336481888433172232592886456975) * 10^40
        + 1136244997376441486594899610610543654112) * 10^40
        + 8435843472399234742467826675825809861297) * 10^40
        + 7553726604572638898290980406490538984971) * 10^40
        + 8191146122563997526894380479532302561986) * 10^40
        + 3652953757819181169059683670275220497417) : ℚ) /
        (((((((((((2415086085061 * 10^40
        + 3679615759460835609864357320512548917859) * 10^40
        + 5266691121423046893431383357333932604326) * 10^40
        + 4962475369856295934274942927582512455083) * 10^40
        + 6553721244005086338305916282547776659231) * 10^40
        + 4380148924460011979449439550536524365387) * 10^40
        + 8852063707820738542410615316911281192216) * 10^40
        + 6497302276671296798869319888602721161108) * 10^40
        + 1016719367857166990108187873684623360665) * 10^40
        + 1272452623607943687990382018905749832987) * 10^40
        + 9432606064591228591318080930535068020883) * 10^40
        + 8169808381259557964481141272885650784256)),
    (((-((((((((4201427753256835205 * 10^40
        + 947770976965551417033802694482388272773) * 10^40
        + 756480357765148060249137884751465114090) * 10^40
        + 5015654550315301462163954495582956552352) * 10^40
        + 1846037711956673171443391353845131223914) * 10^40
        + 8563579795089124864689391410373132969307) * 10^40
        + 2211870573868693941096675508181768774944) * 10^40
        + 4003858288724163300951973094409727269237) * 10^40
        + 2588859709991326608206568083482185665959)) : ℚ) /
        ((((((((3255 * 10^40
        + 8088909332411606420874479890117859410781) * 10^40
        + 9735486973677054664311958828409110338368) * 10^40
        + 4001179604350233615630961045364935855152) * 10^40
        + 5558016987430444017757892323707729369013) * 10^40
        + 867171414809169566951395850392511490345) * 10^40
        + 274198993091977585704002288110142743541) * 10^40
        + 5573263342405911900873947817888183352348) * 10^40
        + 6062936564719639259243885492301079773184)))

noncomputable def batchN02703MinusP016Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP016BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP016Center2558‖ ≤ batchN02703MinusP016Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP016Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP016Input2558]
  have hs : compactExp2547 batchN02703MinusP016Input2558 14 =
      (batchN02703MinusP016Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP016Input2558 14).2 : ℝ) =
      batchN02703MinusP016Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP016Error2558]
  have h := compactExp_error2547 batchN02703MinusP016Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP016Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP016Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP016DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨16, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP016Factor2558 * embedPair2542 batchN02703MinusP016Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP016Factor2558 : ℝ) * batchN02703MinusP016Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP016Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP016Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP016BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP016Factor2558)

def batchN02703MinusP017Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((1070173574585656387116767259 : ℚ) /
        118059162071741130342400000000))

def batchN02703MinusP017Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP017Factor2558 : RatPair2542 :=
    ((((((((((((((302114093213717359214089446839784 *
    10^40
        + 9540103105718875673169178541440037300059) * 10^40
        + 3066126944444573547819969140801547321738) * 10^40
        + 4203937595767446797762763924737516545531) * 10^40
        + 295605040708386965670056920827498412332) * 10^40
        + 5811504314035020198677036662205868654962) * 10^40
        + 699015928408567068720328208443678523371) * 10^40
        + 6220112524967360560871671870606863827717) * 10^40
        + 1854458763946144650292375912673930278793) * 10^40
        + 4131897517588779097644529806449046942915) * 10^40
        + 1293359663894953288000613212306500110491) * 10^40
        + 9972654261157203180607421617887475844113) : ℚ) /
        (((((((((((9660344340245 * 10^40
        + 4718463037843342439457429282050195671438) * 10^40
        + 1066764485692187573725533429335730417305) * 10^40
        + 9849901479425183737099771710330049820334) * 10^40
        + 6214884976020345353223665130191106636925) * 10^40
        + 7520595697840047917797758202146097461551) * 10^40
        + 5408254831282954169642461267645124768866) * 10^40
        + 5989209106685187195477279554410884644432) * 10^40
        + 4066877471428667960432751494738493442660) * 10^40
        + 5089810494431774751961528075622999331951) * 10^40
        + 7730424258364914365272323722140272083535) * 10^40
        + 2679233525038231857924565091542603137024)),
    (((-((((((((37240488763383153896 * 10^40
        + 1657339809876177088206668364605254143321) * 10^40
        + 9731784993608073080561791767272544294570) * 10^40
        + 1153276146340119306668722894218534255807) * 10^40
        + 1821089339447607719527179647115165567672) * 10^40
        + 8132291097319834629647184636569417408522) * 10^40
        + 2350810097528879689773165207299901411128) * 10^40
        + 6027794431014834941113362163344253823067) * 10^40
        + 6275972602423233039078790327206654282173)) : ℚ) /
        ((((((((26046 * 10^40
        + 4711274659292851366995839120942875286255) * 10^40
        + 7883895789416437314495670627272882706947) * 10^40
        + 2009436834801868925047688362919486841220) * 10^40
        + 4464135899443552142063138589661834952104) * 10^40
        + 6937371318473356535611166803140091922760) * 10^40
        + 2193591944735820685632018304881141948332) * 10^40
        + 4586106739247295206991582543105466818788) * 10^40
        + 8503492517757114073951083938408638185472)))

noncomputable def batchN02703MinusP017Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP017BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP017Center2558‖ ≤ batchN02703MinusP017Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP017Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP017Input2558]
  have hs : compactExp2547 batchN02703MinusP017Input2558 14 =
      (batchN02703MinusP017Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP017Input2558 14).2 : ℝ) =
      batchN02703MinusP017Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP017Error2558]
  have h := compactExp_error2547 batchN02703MinusP017Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP017Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP017Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP017DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨17, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP017Factor2558 * embedPair2542 batchN02703MinusP017Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP017Factor2558 : ℝ) * batchN02703MinusP017Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP017Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP017Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP017BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP017Factor2558)

def batchN02703MinusP018Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((277400649960019035138814621 : ℚ) /
        29514790517935282585600000000))

def batchN02703MinusP018Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP018Factor2558 : RatPair2542 := ((((((((((((((18882130824870252021079088305022
    *
    10^40
        + 9285236394487844907594345443317333824719) * 10^40
        + 5145264805038177464846705487415166468195) * 10^40
        + 9308154678105593084714031460385555681620) * 10^40
        + 483451934198505331160065618957249410369) * 10^40
        + 634191700995864341932209632503463700460) * 10^40
        + 7262287844009156931158359454002300338711) * 10^40
        + 7511646668630074544656997642576728950906) * 10^40
        + 3407343797055187207892274183502646804451) * 10^40
        + 7364385485474485585601895370373556221777) * 10^40
        + 689473194868608299460179968037581253418) * 10^40
        + 3834046448658847928722532807607040891393) : ℚ) /
        (((((((((((603771521265 * 10^40
        + 3419903939865208902466089330128137229464) * 10^40
        + 8816672780355761723357845839333483151081) * 10^40
        + 6240618842464073983568735731895628113770) * 10^40
        + 9138430311001271584576479070636944164807) * 10^40
        + 8595037231115002994862359887634131091346) * 10^40
        + 9713015926955184635602653829227820298054) * 10^40
        + 1624325569167824199717329972150680290277) * 10^40
        + 254179841964291747527046968421155840166) * 10^40
        + 2818113155901985921997595504726437458246) * 10^40
        + 9858151516147807147829520232633767005220) * 10^40
        + 9542452095314889491120285318221412696064)),
    (((-((((((((1809963828484144198 * 10^40
        + 4247610660285321507856731181334964198293) * 10^40
        + 2198874273008826323252466862903171077815) * 10^40
        + 4552951860478384394211632713865362404350) * 10^40
        + 7551484460160208990047832866700535599304) * 10^40
        + 5122773506929517756337548202291578685195) * 10^40
        + 8756464500998256517906661422267075916398) * 10^40
        + 3994428542731239675826191391459040258394) * 10^40
        + 7664596942749276225369357557055725274321)) : ℚ) /
        ((((((((1220 * 10^40
        + 9283340999654352407827929958794197279043) * 10^40
        + 2400807615128895499116984560653416376888) * 10^40
        + 1500442351631337605861610392011850945682) * 10^40
        + 2084256370286416506659209621390398513379) * 10^40
        + 9075189280553438587606773443897191808879) * 10^40
        + 3852824622409491594639000858041303528828) * 10^40
        + 839973753402216962827730431708068757130) * 10^40
        + 7273601211769864722216457059612904914944)))

noncomputable def batchN02703MinusP018Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP018BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP018Center2558‖ ≤ batchN02703MinusP018Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP018Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP018Input2558]
  have hs : compactExp2547 batchN02703MinusP018Input2558 14 =
      (batchN02703MinusP018Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP018Input2558 14).2 : ℝ) =
      batchN02703MinusP018Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP018Error2558]
  have h := compactExp_error2547 batchN02703MinusP018Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP018Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP018Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP018DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨18, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP018Factor2558 * embedPair2542 batchN02703MinusP018Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP018Factor2558 : ℝ) * batchN02703MinusP018Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP018Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP018Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP018BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP018Factor2558)

def batchN02703MinusP019Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((59043078963632663143756047 : ℚ) /
        5902958103587056517120000000))

def batchN02703MinusP019Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP019Factor2558 : RatPair2542 := ((((((((((((((18882130822995737531968473431573
    *
    10^40
        + 6358642329768966582566899526567959366925) * 10^40
        + 6166496187548626967065328359777363877850) * 10^40
        + 4434312956893142399915068700136697461524) * 10^40
        + 2176155542451338158767101489992069057332) * 10^40
        + 7482598430122875868766096527431970547894) * 10^40
        + 8069768042493856432303445197890844770069) * 10^40
        + 4079359386689604776045131024324050474915) * 10^40
        + 339776113090139350707756256567013090737) * 10^40
        + 6091955813072515684154949344147464899694) * 10^40
        + 9235292980041942122767868675523472741225) * 10^40
        + 1387317744176809102605564461887278599217) : ℚ) /
        (((((((((((603771521265 * 10^40
        + 3419903939865208902466089330128137229464) * 10^40
        + 8816672780355761723357845839333483151081) * 10^40
        + 6240618842464073983568735731895628113770) * 10^40
        + 9138430311001271584576479070636944164807) * 10^40
        + 8595037231115002994862359887634131091346) * 10^40
        + 9713015926955184635602653829227820298054) * 10^40
        + 1624325569167824199717329972150680290277) * 10^40
        + 254179841964291747527046968421155840166) * 10^40
        + 2818113155901985921997595504726437458246) * 10^40
        + 9858151516147807147829520232633767005220) * 10^40
        + 9542452095314889491120285318221412696064)),
    (((-((((((((214022243961200535 * 10^40
        + 9256343593012954080248283795370516257246) * 10^40
        + 326090414465184198413748526347644194009) * 10^40
        + 1167555725393967814043155171745111458287) * 10^40
        + 6952327585321365648807669723175144759447) * 10^40
        + 6746642190439327831196405228688380033467) * 10^40
        + 7535475263323179763068271216806926519546) * 10^40
        + 8712411317716558855082443674201249686886) * 10^40
        + 3852688298233451915513685829080810560655)) : ℚ) /
        ((((((((135 * 10^40
        + 6587037888850483600869769995421577475449) * 10^40
        + 2488978623903210611012998284517046264098) * 10^40
        + 6833382483514593067317956710223538993964) * 10^40
        + 6898250707809601834073245513487822057042) * 10^40
        + 2119465475617048731956308160433021312097) * 10^40
        + 7094758291378832399404333428671255947647) * 10^40
        + 5648885972600246329203081159078674306347) * 10^40
        + 8585955690196651635801828562179211657216)))

noncomputable def batchN02703MinusP019Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP019BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP019Center2558‖ ≤ batchN02703MinusP019Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP019Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP019Input2558]
  have hs : compactExp2547 batchN02703MinusP019Input2558 14 =
      (batchN02703MinusP019Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP019Input2558 14).2 : ℝ) =
      batchN02703MinusP019Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP019Error2558]
  have h := compactExp_error2547 batchN02703MinusP019Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP019Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP019Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP019DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨19, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP019Factor2558 * embedPair2542 batchN02703MinusP019Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP019Factor2558 : ℝ) * batchN02703MinusP019Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP019Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP019Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP019BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP019Factor2558)

def batchN02703MinusP020Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((1258350022051737949215779723 : ℚ) /
        118059162071741130342400000000))

def batchN02703MinusP020Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP020Factor2558 : RatPair2542 :=
    ((((((((((((((302114093133199616576547148309804 *
    10^40
        + 9108925174182026288041573788628464650313) * 10^40
        + 13184879432629975499173695504273424890) * 10^40
        + 486255305208582307263056155978071267787) * 10^40
        + 3780081662609422340839870514255488164845) * 10^40
        + 1125371932717503125061677350564798595162) * 10^40
        + 923924899116044651562673371980868479115) * 10^40
        + 918832773053730688889751961894388128646) * 10^40
        + 8594385025084754451517939533639552747552) * 10^40
        + 6203041159524400709041001955639293331343) * 10^40
        + 9177258645042298180152200114504732017140) * 10^40
        + 1634812132732520569690847964472235973041) : ℚ) /
        (((((((((((9660344340245 * 10^40
        + 4718463037843342439457429282050195671438) * 10^40
        + 1066764485692187573725533429335730417305) * 10^40
        + 9849901479425183737099771710330049820334) * 10^40
        + 6214884976020345353223665130191106636925) * 10^40
        + 7520595697840047917797758202146097461551) * 10^40
        + 5408254831282954169642461267645124768866) * 10^40
        + 5989209106685187195477279554410884644432) * 10^40
        + 4066877471428667960432751494738493442660) * 10^40
        + 5089810494431774751961528075622999331951) * 10^40
        + 7730424258364914365272323722140272083535) * 10^40
        + 2679233525038231857924565091542603137024)),
    (((-((((((((131366268897203082314 * 10^40
        + 8600698479311625679086498473187579420618) * 10^40
        + 1682276090557731927599586603923136228884) * 10^40
        + 954866933984063841834943070921776799469) * 10^40
        + 459316819745784875674918055660851706924) * 10^40
        + 5422392482281121706084221003020838533432) * 10^40
        + 7715459367513180964064150927645263845476) * 10^40
        + 1813144569536601420056499205240552738651) * 10^40
        + 6244188033694001375857948071939921339079)) : ℚ) /
        ((((((((78139 * 10^40
        + 4133823977878554100987517362828625858767) * 10^40
        + 3651687368249311943487011881818648120841) * 10^40
        + 6028310504405606775143065088758460523661) * 10^40
        + 3392407698330656426189415768985504856314) * 10^40
        + 812113955420069606833500409420275768280) * 10^40
        + 6580775834207462056896054914643425844997) * 10^40
        + 3758320217741885620974747629316400456366) * 10^40
        + 5510477553271342221853251815225914556416)))

noncomputable def batchN02703MinusP020Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP020BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP020Center2558‖ ≤ batchN02703MinusP020Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP020Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP020Input2558]
  have hs : compactExp2547 batchN02703MinusP020Input2558 14 =
      (batchN02703MinusP020Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP020Input2558 14).2 : ℝ) =
      batchN02703MinusP020Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP020Error2558]
  have h := compactExp_error2547 batchN02703MinusP020Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP020Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP020Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP020DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨20, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP020Factor2558 * embedPair2542 batchN02703MinusP020Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP020Factor2558 : ℝ) * batchN02703MinusP020Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP020Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP020Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP020BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP020Factor2558)

def batchN02703MinusP021Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((1323017156608362402082742379 : ℚ) /
        118059162071741130342400000000))

def batchN02703MinusP021Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP021Factor2558 : RatPair2542 :=
    ((((((((((((((302114093102525004204799936018899 *
    10^40
        + 4941820468983399421612072300387046984723) * 10^40
        + 8345628867220102319211876370860618775425) * 10^40
        + 9202235663427878439248172822948792454920) * 10^40
        + 4068409541207841699867746517598017885650) * 10^40
        + 1054990033237057977495735074634516820094) * 10^40
        + 3570473087619831535797161699527982514858) * 10^40
        + 6252105514222378926738385470615177172145) * 10^40
        + 269089229153422545273077585756073932496) * 10^40
        + 1785039148721568508484664176815330785815) * 10^40
        + 163369532679055484025557395433909370569) * 10^40
        + 1686380724977483880568935541206489452273) : ℚ) /
        (((((((((((9660344340245 * 10^40
        + 4718463037843342439457429282050195671438) * 10^40
        + 1066764485692187573725533429335730417305) * 10^40
        + 9849901479425183737099771710330049820334) * 10^40
        + 6214884976020345353223665130191106636925) * 10^40
        + 7520595697840047917797758202146097461551) * 10^40
        + 5408254831282954169642461267645124768866) * 10^40
        + 5989209106685187195477279554410884644432) * 10^40
        + 4066877471428667960432751494738493442660) * 10^40
        + 5089810494431774751961528075622999331951) * 10^40
        + 7730424258364914365272323722140272083535) * 10^40
        + 2679233525038231857924565091542603137024)),
    (((-((((((((46039078820927405886 * 10^40
        + 2164123473966378921236957062354281866763) * 10^40
        + 5119377407108319664040290468384559328810) * 10^40
        + 2624514234524196512260368076726147928855) * 10^40
        + 5788168225594677157524683270087934803652) * 10^40
        + 1179083594023160100576204696836390545507) * 10^40
        + 6815571557177251827851369593538668106716) * 10^40
        + 5944298671914006331159274057937915474980) * 10^40
        + 8304260739676645080108912436318073843533)) : ℚ) /
        ((((((((26046 * 10^40
        + 4711274659292851366995839120942875286255) * 10^40
        + 7883895789416437314495670627272882706947) * 10^40
        + 2009436834801868925047688362919486841220) * 10^40
        + 4464135899443552142063138589661834952104) * 10^40
        + 6937371318473356535611166803140091922760) * 10^40
        + 2193591944735820685632018304881141948332) * 10^40
        + 4586106739247295206991582543105466818788) * 10^40
        + 8503492517757114073951083938408638185472)))

noncomputable def batchN02703MinusP021Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP021BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP021Center2558‖ ≤ batchN02703MinusP021Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP021Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP021Input2558]
  have hs : compactExp2547 batchN02703MinusP021Input2558 14 =
      (batchN02703MinusP021Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP021Input2558 14).2 : ℝ) =
      batchN02703MinusP021Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP021Error2558]
  have h := compactExp_error2547 batchN02703MinusP021Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP021Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP021Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP021DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨21, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP021Factor2558 * embedPair2542 batchN02703MinusP021Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP021Factor2558 : ℝ) * batchN02703MinusP021Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP021Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP021Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP021BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP021Factor2558)

def batchN02703MinusP022Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((271223236161618499784975161 : ℚ) /
        23611832414348226068480000000))

def batchN02703MinusP022Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP022Factor2558 : RatPair2542 :=
    ((((((((((((((302114093086229972832307803919982 *
    10^40
        + 8595914006209930761735441084172183944486) * 10^40
        + 9168608041759357074809416544992946525561) * 10^40
        + 1036227155197128658487626760190781506215) * 10^40
        + 7471832548579644957460102142185726577964) * 10^40
        + 3275673176682416541095027425113022131398) * 10^40
        + 6857668213077078510249553236391274587888) * 10^40
        + 4125577979395786917428519819283875137574) * 10^40
        + 1236456013913120787015404452987529580399) * 10^40
        + 2267245132738123932502343449213913650415) * 10^40
        + 4897532360200920208224111167378655194631) * 10^40
        + 2688789165343005942435732104635660144897) : ℚ) /
        (((((((((((9660344340245 * 10^40
        + 4718463037843342439457429282050195671438) * 10^40
        + 1066764485692187573725533429335730417305) * 10^40
        + 9849901479425183737099771710330049820334) * 10^40
        + 6214884976020345353223665130191106636925) * 10^40
        + 7520595697840047917797758202146097461551) * 10^40
        + 5408254831282954169642461267645124768866) * 10^40
        + 5989209106685187195477279554410884644432) * 10^40
        + 4066877471428667960432751494738493442660) * 10^40
        + 5089810494431774751961528075622999331951) * 10^40
        + 7730424258364914365272323722140272083535) * 10^40
        + 2679233525038231857924565091542603137024)),
    (((-((((((((141572630618575924987 * 10^40
        + 1074190359452705859915570237065683493961) * 10^40
        + 445562925536938669464832884633898755685) * 10^40
        + 3208625767922665041246360466874274325901) * 10^40
        + 7524355113566144008223825982396284404455) * 10^40
        + 4159899496363733804530234405597177807926) * 10^40
        + 8353354687075562078455925153262245389263) * 10^40
        + 3838745424690952464556466873326020242570) * 10^40
        + 3443389802897281792624532575571256360785)) : ℚ) /
        ((((((((78139 * 10^40
        + 4133823977878554100987517362828625858767) * 10^40
        + 3651687368249311943487011881818648120841) * 10^40
        + 6028310504405606775143065088758460523661) * 10^40
        + 3392407698330656426189415768985504856314) * 10^40
        + 812113955420069606833500409420275768280) * 10^40
        + 6580775834207462056896054914643425844997) * 10^40
        + 3758320217741885620974747629316400456366) * 10^40
        + 5510477553271342221853251815225914556416)))

noncomputable def batchN02703MinusP022Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP022BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP022Center2558‖ ≤ batchN02703MinusP022Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP022Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP022Input2558]
  have hs : compactExp2547 batchN02703MinusP022Input2558 14 =
      (batchN02703MinusP022Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP022Input2558 14).2 : ℝ) =
      batchN02703MinusP022Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP022Error2558]
  have h := compactExp_error2547 batchN02703MinusP022Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP022Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP022Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP022DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨22, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP022Factor2558 * embedPair2542 batchN02703MinusP022Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP022Factor2558 : ℝ) * batchN02703MinusP022Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP022Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP022Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP022BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP022Factor2558)

def batchN02703MinusP023Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((725773409053467230818592861 : ℚ) /
        59029581035870565171200000000))

def batchN02703MinusP023Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP023Factor2558 : RatPair2542 := ((((((((((((((75528523259248614463431935706569
    *
    10^40
        + 2750568308994392510584729654815617242183) * 10^40
        + 1847079144137594654717201231018831212605) * 10^40
        + 566595437073599357173219202513567068770) * 10^40
        + 2800716570039195593262691274024140927914) * 10^40
        + 2321062027944354020046365208872324298343) * 10^40
        + 5678452014116090901572811812175867922363) * 10^40
        + 4789004694431348465346917074354604876984) * 10^40
        + 4473914796353436185570561005016249936620) * 10^40
        + 7789084471463641651162209645954834173629) * 10^40
        + 373020800440732090102182723823715544534) * 10^40
        + 3626241112415565459917139353584834046849) : ℚ) /
        (((((((((((2415086085061 * 10^40
        + 3679615759460835609864357320512548917859) * 10^40
        + 5266691121423046893431383357333932604326) * 10^40
        + 4962475369856295934274942927582512455083) * 10^40
        + 6553721244005086338305916282547776659231) * 10^40
        + 4380148924460011979449439550536524365387) * 10^40
        + 8852063707820738542410615316911281192216) * 10^40
        + 6497302276671296798869319888602721161108) * 10^40
        + 1016719367857166990108187873684623360665) * 10^40
        + 1272452623607943687990382018905749832987) * 10^40
        + 9432606064591228591318080930535068020883) * 10^40
        + 8169808381259557964481141272885650784256)),
    (((-((((((((18941896757257175696 * 10^40
        + 5886631396883342500936226760653312469734) * 10^40
        + 3448822416173049595494227907297126002300) * 10^40
        + 3557575063465707676196138746343130610255) * 10^40
        + 9084264277252265951305593966520327342103) * 10^40
        + 8746635902889249472423591691793992915378) * 10^40
        + 8021976993547897856597624241664616219435) * 10^40
        + 1539229364426658080007682492065854066576) * 10^40
        + 3427521777626587874389396794392385227537)) : ℚ) /
        ((((((((9767 * 10^40
        + 4266727997234819262623439670353578232345) * 10^40
        + 9206460921031163992935876485227331015105) * 10^40
        + 2003538813050700846892883136094807565457) * 10^40
        + 6674050962291332053273676971123188107039) * 10^40
        + 2601514244427508700854187551177534471035) * 10^40
        + 822596979275932757112006864330428230624) * 10^40
        + 6719790027217735702621843453664550057045) * 10^40
        + 8188809694158917777731656476903239319552)))

noncomputable def batchN02703MinusP023Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP023BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP023Center2558‖ ≤ batchN02703MinusP023Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP023Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP023Input2558]
  have hs : compactExp2547 batchN02703MinusP023Input2558 14 =
      (batchN02703MinusP023Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP023Input2558 14).2 : ℝ) =
      batchN02703MinusP023Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP023Error2558]
  have h := compactExp_error2547 batchN02703MinusP023Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP023Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP023Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP023DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨23, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP023Factor2558 * embedPair2542 batchN02703MinusP023Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP023Factor2558 : ℝ) * batchN02703MinusP023Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP023Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP023Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP023BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP023Factor2558)

def batchN02703MinusP024Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((747701437233061660886831299 : ℚ) /
        59029581035870565171200000000))

def batchN02703MinusP024Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP024Factor2558 : RatPair2542 := ((((((((((((((75528523253311328195390179427124
    *
    10^40
        + 6934480458662209491087231942246187962543) * 10^40
        + 3867674537340783128787688817512078629027) * 10^40
        + 730715115257558655227380360406002307122) * 10^40
        + 6358576432845653330279501657716411721923) * 10^40
        + 5146488589742456671991587727340004517426) * 10^40
        + 7810691556312815341936017438055269171665) * 10^40
        + 8575460987414025898605474231651194801892) * 10^40
        + 5806206923623077902020112287725254201247) * 10^40
        + 7746284526905234769306927046386020972181) * 10^40
        + 7148081336107343110905513942275872805053) * 10^40
        + 5759140184887292840461572731295764977729) : ℚ) /
        (((((((((((2415086085061 * 10^40
        + 3679615759460835609864357320512548917859) * 10^40
        + 5266691121423046893431383357333932604326) * 10^40
        + 4962475369856295934274942927582512455083) * 10^40
        + 6553721244005086338305916282547776659231) * 10^40
        + 4380148924460011979449439550536524365387) * 10^40
        + 8852063707820738542410615316911281192216) * 10^40
        + 6497302276671296798869319888602721161108) * 10^40
        + 1016719367857166990108187873684623360665) * 10^40
        + 1272452623607943687990382018905749832987) * 10^40
        + 9432606064591228591318080930535068020883) * 10^40
        + 8169808381259557964481141272885650784256)),
    (((-((((((((19514194447642579079 * 10^40
        + 730272081389059384744374042970480702800) * 10^40
        + 3867979837176507746697296472505555515527) * 10^40
        + 9087214375951431621930623357529649791408) * 10^40
        + 1829154434576002050965328865656608890157) * 10^40
        + 533113777181881541074116095402173527927) * 10^40
        + 7412644393736755055188176740957448308123) * 10^40
        + 9363734819779428816857767772513008141897) * 10^40
        + 6361324807680610138096980654299142912463)) : ℚ) /
        ((((((((9767 * 10^40
        + 4266727997234819262623439670353578232345) * 10^40
        + 9206460921031163992935876485227331015105) * 10^40
        + 2003538813050700846892883136094807565457) * 10^40
        + 6674050962291332053273676971123188107039) * 10^40
        + 2601514244427508700854187551177534471035) * 10^40
        + 822596979275932757112006864330428230624) * 10^40
        + 6719790027217735702621843453664550057045) * 10^40
        + 8188809694158917777731656476903239319552)))

noncomputable def batchN02703MinusP024Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP024BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP024Center2558‖ ≤ batchN02703MinusP024Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP024Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP024Input2558]
  have hs : compactExp2547 batchN02703MinusP024Input2558 14 =
      (batchN02703MinusP024Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP024Input2558 14).2 : ℝ) =
      batchN02703MinusP024Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP024Error2558]
  have h := compactExp_error2547 batchN02703MinusP024Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP024Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP024Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP024DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨24, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP024Factor2558 * embedPair2542 batchN02703MinusP024Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP024Factor2558 : ℝ) * batchN02703MinusP024Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP024Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP024Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP024BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP024Factor2558)

def batchN02703MinusP025Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((24224848776857806967243361 : ℚ) /
        1844674407370955161600000000))

def batchN02703MinusP025Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP025Factor2558 : RatPair2542 := ((((((((((((((73758323482048215675829260872 *
    10^40
        + 3419231935671001038431213571480652976710) * 10^40
        + 9095270833100763466030435348497678872041) * 10^40
        + 6717681205331140521616405052428585211276) * 10^40
        + 7110604670608569273456732117737393514368) * 10^40
        + 7205014229821288111535007284292594500600) * 10^40
        + 7392686355491842970221492247413212552002) * 10^40
        + 8903632545124863258531400282418962413387) * 10^40
        + 2339549082776004596233549070688734253633) * 10^40
        + 1071802322252761022461555446990279698573) * 10^40
        + 8791407609716876743718569409194264149045) * 10^40
        + 6227788289297608887555362346101722966713) : ℚ) /
        (((((((((((2358482504 * 10^40
        + 9427421499765098472275258161445813036052) * 10^40
        + 5971940128048264694231866585309896418558) * 10^40
        + 9125939917353375288998315373952717297319) * 10^40
        + 4176321993402348717127251871369675563143) * 10^40
        + 7807011864184042980448681093311070824575) * 10^40
        + 5741066468464668689982822866520421173039) * 10^40
        + 2740720021754561813280145820203713594883) * 10^40
        + 8946305390007673014638777527220395140000) * 10^40
        + 6495383254515242132507803107440337646321) * 10^40
        + 2772883404359952371671209063408725652364) * 10^40
        + 1443525203497323787074688614524302393344)),
    (((-((((((((205808011239495 * 10^40
        + 828687108983653660757755500512537618647) * 10^40
        + 669343711908594505523989597235500561857) * 10^40
        + 5036207734389461105306713020900222275456) * 10^40
        + 5578234994044858038444267173405618964535) * 10^40
        + 4024948833001432918163080778806261303117) * 10^40
        + 9431454547586196240829812074398761819819) * 10^40
        + 6830594241549380467666399054533011649990) * 10^40
        + 3282888498016461034389722907828642959807)) : ℚ) /
        (((((((993594021891247912793605788570865413190 * 10^40
        + 263053451140554109334238035852917758494) * 10^40
        + 2129028356311167914844227019074870756099) * 10^40
        + 952318054717633985718315365366324088420) * 10^40
        + 6852138280377649205614225811640942154281) * 10^40
        + 3215645574920443480761282470772952580039) * 10^40
        + 7809313148905713071041896787958309575907) * 10^40
        + 9696229948015280750709815792403939852288)))

noncomputable def batchN02703MinusP025Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP025BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP025Center2558‖ ≤ batchN02703MinusP025Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP025Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP025Input2558]
  have hs : compactExp2547 batchN02703MinusP025Input2558 14 =
      (batchN02703MinusP025Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP025Input2558 14).2 : ℝ) =
      batchN02703MinusP025Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP025Error2558]
  have h := compactExp_error2547 batchN02703MinusP025Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP025Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP025Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP025DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨25, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP025Factor2558 * embedPair2542 batchN02703MinusP025Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP025Factor2558 : ℝ) * batchN02703MinusP025Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP025Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP025Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP025BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP025Factor2558)

def batchN02703MinusP026Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((50205789328760982418175229 : ℚ) /
        3689348814741910323200000000))

def batchN02703MinusP026Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP026Factor2558 : RatPair2542 := ((((((((((((((295033293896357182381633237494 *
    10^40
        + 8034954467378999687458398387172443806075) * 10^40
        + 2451495305876983144855580250922816891486) * 10^40
        + 5864456312137724334797957425617331517668) * 10^40
        + 452056523533240930087036005615537555125) * 10^40
        + 1439791305616262588177391278187477478698) * 10^40
        + 5356376594634349278255228399118492934400) * 10^40
        + 6619680884470632504048918581002076337990) * 10^40
        + 1659828289474707942672745777478732803932) * 10^40
        + 7684690679494931466223450794046910484074) * 10^40
        + 8022887362047436278829644146213626430390) * 10^40
        + 2983726873964613001182867851759829678529) : ℚ) /
        (((((((((((9433930019 * 10^40
        + 7709685999060393889101032645783252144210) * 10^40
        + 3887760512193058776927466341239585674235) * 10^40
        + 6503759669413501155993261495810869189277) * 10^40
        + 6705287973609394868509007485478702252575) * 10^40
        + 1228047456736171921794724373244283298302) * 10^40
        + 2964265873858674759931291466081684692157) * 10^40
        + 962880087018247253120583280814854379535) * 10^40
        + 5785221560030692058555110108881580560002) * 10^40
        + 5981533018060968530031212429761350585285) * 10^40
        + 1091533617439809486684836253634902609456) * 10^40
        + 5774100813989295148298754458097209573376)),
    (((-((((((((1706141284846076 * 10^40
        + 2059731594894585184602971165870971869132) * 10^40
        + 4215892602618764278329402611706931743053) * 10^40
        + 5808632028414304163619164451851856176243) * 10^40
        + 9745824414281150527223664545705295686349) * 10^40
        + 6988564915594114665210719803599609385512) * 10^40
        + 5081880924382316519235323642304860330517) * 10^40
        + 5475462811033585894405058661393890812376) * 10^40
        + 2260334947836048334814760199142299113851)) : ℚ) /
        (((((((7948752175129983302348846308566923305520 * 10^40
        + 2104427609124432874673904286823342067953) * 10^40
        + 7032226850489343318753816152598966048792) * 10^40
        + 7618544437741071885746522922930592707365) * 10^40
        + 4817106243021193644913806493127537234250) * 10^40
        + 5725164599363547846090259766183620640318) * 10^40
        + 2474505191245704568335174303666476607263) * 10^40
        + 7569839584122246005678526339231518818304)))

noncomputable def batchN02703MinusP026Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP026BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP026Center2558‖ ≤ batchN02703MinusP026Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP026Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP026Input2558]
  have hs : compactExp2547 batchN02703MinusP026Input2558 14 =
      (batchN02703MinusP026Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP026Input2558 14).2 : ℝ) =
      batchN02703MinusP026Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP026Error2558]
  have h := compactExp_error2547 batchN02703MinusP026Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP026Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP026Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP026DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨26, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP026Factor2558 * embedPair2542 batchN02703MinusP026Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP026Factor2558 : ℝ) * batchN02703MinusP026Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP026Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP026Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP026BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP026Factor2558)

def batchN02703MinusP027Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((105479774007600136776241459 : ℚ) /
        7378697629483820646400000000))

def batchN02703MinusP027Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP027Factor2558 : RatPair2542 := ((((((((((((((1180133175393677951402899544129
    * 10^40
        + 7931283276159506700655468706243019424224) * 10^40
        + 6375763673967137859891813354610844236067) * 10^40
        + 9976678314115358081870740943663175769471) * 10^40
        + 6459622980785818521784194782551717225826) * 10^40
        + 351414846445700272131187175532115450102) * 10^40
        + 2451479374653105195497940137093473170241) * 10^40
        + 6815430118838341319587259452240152671518) * 10^40
        + 1819928333421293576806886109030980740067) * 10^40
        + 1095753745091676866046178857264782253689) * 10^40
        + 1363809820381337797366586241094448847393) * 10^40
        + 8565656329490006652608226748446030141153) : ℚ) /
        (((((((((((37735720079 * 10^40
        + 838743996241575556404130583133008576841) * 10^40
        + 5551042048772235107709865364958342696942) * 10^40
        + 6015038677654004623973045983243476757110) * 10^40
        + 6821151894437579474036029941914809010300) * 10^40
        + 4912189826944687687178897492977133193209) * 10^40
        + 1857063495434699039725165864326738768628) * 10^40
        + 3851520348072989012482333123259417518142) * 10^40
        + 3140886240122768234220440435526322240010) * 10^40
        + 3926132072243874120124849719045402341140) * 10^40
        + 4366134469759237946739345014539610437826) * 10^40
        + 3096403255957180593195017832388838293504)),
    (((-((((((((43014178138438366 * 10^40
        + 1466503741601617727067486191696939073364) * 10^40
        + 4770667450202280108980210059294526362948) * 10^40
        + 5695853357961377871330744943719488799841) * 10^40
        + 9408917450076366565682297774017372337341) * 10^40
        + 5459953310859100719689337577823338804862) * 10^40
        + 9788169448290831323490052224863299804143) * 10^40
        + 3804823179949685500183245333254264364456) * 10^40
        + 717602414959786563792560979087283504479)) : ℚ) /
        ((((((((19 * 10^40
        + 770052203119599256372311405606159332485) * 10^40
        + 506262618986388992173702883760209630888) * 10^40
        + 8773444411744239650091587662375185171026) * 10^40
        + 2845066505785725257916550150334224976771) * 10^40
        + 5610549832508647477931355835060893622013) * 10^40
        + 7403950384725148306166234388406895367637) * 10^40
        + 9388124589896909640044183287995438574330) * 10^40
        + 1676150018933904136284632141556451639296)))

noncomputable def batchN02703MinusP027Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP027BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP027Center2558‖ ≤ batchN02703MinusP027Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP027Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP027Input2558]
  have hs : compactExp2547 batchN02703MinusP027Input2558 14 =
      (batchN02703MinusP027Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP027Input2558 14).2 : ℝ) =
      batchN02703MinusP027Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP027Error2558]
  have h := compactExp_error2547 batchN02703MinusP027Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP027Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP027Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP027DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨27, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP027Factor2558 * embedPair2542 batchN02703MinusP027Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP027Factor2558 : ℝ) * batchN02703MinusP027Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP027Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP027Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP027BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP027Factor2558)

def batchN02703MinusP028Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((429945369100667103165553159 : ℚ) /
        29514790517935282585600000000))

def batchN02703MinusP028Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP028Factor2558 : RatPair2542 := ((((((((((((((18882130805042440892900486471627
    *
    10^40
        + 473279871318383406804261060274137505536) * 10^40
        + 2388762242978762575767051130741873025701) * 10^40
        + 7433440810895086891716769429528000694720) * 10^40
        + 2762576388580341518901717369893672347414) * 10^40
        + 5947058326305911566728014843008685483448) * 10^40
        + 6261888448537053449212149130013080720906) * 10^40
        + 5184080859217180214689160569214527793898) * 10^40
        + 1680982188447462116191720899852855337241) * 10^40
        + 5057221068078284394996458551272753184) * 10^40
        + 3252449900865612472289649955365830032188) * 10^40
        + 55649386585724783481125921554058187433) : ℚ) /
        (((((((((((603771521265 * 10^40
        + 3419903939865208902466089330128137229464) * 10^40
        + 8816672780355761723357845839333483151081) * 10^40
        + 6240618842464073983568735731895628113770) * 10^40
        + 9138430311001271584576479070636944164807) * 10^40
        + 8595037231115002994862359887634131091346) * 10^40
        + 9713015926955184635602653829227820298054) * 10^40
        + 1624325569167824199717329972150680290277) * 10^40
        + 254179841964291747527046968421155840166) * 10^40
        + 2818113155901985921997595504726437458246) * 10^40
        + 9858151516147807147829520232633767005220) * 10^40
        + 9542452095314889491120285318221412696064)),
    (((-((((((((2805276650641821005 * 10^40
        + 3129528198655553999466210058318348124472) * 10^40
        + 9704392892326514051961974123908996495887) * 10^40
        + 1949823303938697317224898899093635037188) * 10^40
        + 265939435732961098878658001664418165818) * 10^40
        + 4523189964947988138970794707009548800706) * 10^40
        + 5526972510298220005086140312718069334519) * 10^40
        + 392146788207656247966481921707278917604) * 10^40
        + 3973607820471690262385614023026526494299)) : ℚ) /
        ((((((((1220 * 10^40
        + 9283340999654352407827929958794197279043) * 10^40
        + 2400807615128895499116984560653416376888) * 10^40
        + 1500442351631337605861610392011850945682) * 10^40
        + 2084256370286416506659209621390398513379) * 10^40
        + 9075189280553438587606773443897191808879) * 10^40
        + 3852824622409491594639000858041303528828) * 10^40
        + 839973753402216962827730431708068757130) * 10^40
        + 7273601211769864722216457059612904914944)))

noncomputable def batchN02703MinusP028Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP028BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP028Center2558‖ ≤ batchN02703MinusP028Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP028Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP028Input2558]
  have hs : compactExp2547 batchN02703MinusP028Input2558 14 =
      (batchN02703MinusP028Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP028Input2558 14).2 : ℝ) =
      batchN02703MinusP028Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP028Error2558]
  have h := compactExp_error2547 batchN02703MinusP028Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP028Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP028Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP028DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨28, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP028Factor2558 * embedPair2542 batchN02703MinusP028Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP028Factor2558 : ℝ) * batchN02703MinusP028Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP028Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP028Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP028BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP028Factor2558)

def batchN02703MinusP029Input2558 : RatPair2542 := ((((-((385420 * 10^40
        + 678219061623534497381996571440505130843) * 10^40
        + 6144430343825511973057947804995642626229)) : ℚ) /
        ((521614 * 10^40
        + 6395461102620328463706555753488498145190) * 10^40
        + 9516601880638960185675088710860800000000)),
    ((442164854526954039721671803 : ℚ) /
        29514790517935282585600000000))

def batchN02703MinusP029Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchN02703MinusP029Factor2558 : RatPair2542 := ((((((((((((((18882130803084182586061347003672
    *
    10^40
        + 6857444746471278638052627769878467102926) * 10^40
        + 4525830633780408546891016219876054118751) * 10^40
        + 930792576722507181048644680629527476152) * 10^40
        + 5016800895945074202414015710267978981536) * 10^40
        + 2957201263639844732896741453805321557811) * 10^40
        + 1766032507222349833908962141565993228607) * 10^40
        + 7224069026284453408552053170606486494427) * 10^40
        + 7765007343722286106386382285958687310608) * 10^40
        + 5496660800401045902690607724390809661470) * 10^40
        + 9862659802678659307884623773203894289044) * 10^40
        + 1297419833778948467790336411206187881041) : ℚ) /
        (((((((((((603771521265 * 10^40
        + 3419903939865208902466089330128137229464) * 10^40
        + 8816672780355761723357845839333483151081) * 10^40
        + 6240618842464073983568735731895628113770) * 10^40
        + 9138430311001271584576479070636944164807) * 10^40
        + 8595037231115002994862359887634131091346) * 10^40
        + 9713015926955184635602653829227820298054) * 10^40
        + 1624325569167824199717329972150680290277) * 10^40
        + 254179841964291747527046968421155840166) * 10^40
        + 2818113155901985921997595504726437458246) * 10^40
        + 9858151516147807147829520232633767005220) * 10^40
        + 9542452095314889491120285318221412696064)),
    (((-((((((((2885005471088555460 * 10^40
        + 3694586597835546974626657747048265541204) * 10^40
        + 3727356730076816133340853006781463207334) * 10^40
        + 1142371140076525693252907993944773356312) * 10^40
        + 8207391712780676651088518032490459769282) * 10^40
        + 6378220579182470190832461281243379071723) * 10^40
        + 7200407630306740579917411370474191616267) * 10^40
        + 8908693113489584626920326970988356016376) * 10^40
        + 9792954666176419038131569314546714215639)) : ℚ) /
        ((((((((1220 * 10^40
        + 9283340999654352407827929958794197279043) * 10^40
        + 2400807615128895499116984560653416376888) * 10^40
        + 1500442351631337605861610392011850945682) * 10^40
        + 2084256370286416506659209621390398513379) * 10^40
        + 9075189280553438587606773443897191808879) * 10^40
        + 3852824622409491594639000858041303528828) * 10^40
        + 839973753402216962827730431708068757130) * 10^40
        + 7273601211769864722216457059612904914944)))

noncomputable def batchN02703MinusP029Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchN02703MinusP029BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP029Center2558‖ ≤ batchN02703MinusP029Error2558 := by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchN02703MinusP029Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchN02703MinusP029Input2558]
  have hs : compactExp2547 batchN02703MinusP029Input2558 14 =
      (batchN02703MinusP029Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchN02703MinusP029Input2558 14).2 : ℝ) =
      batchN02703MinusP029Error2558 := by
    rw [hs]
    norm_num [batchN02703MinusP029Error2558]
  have h := compactExp_error2547 batchN02703MinusP029Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      batchN02703MinusPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchN02703MinusP029Input2558) :=
          by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchN02703MinusPosition2558, storedWidth, nodeModulation2541,
      embedPair2542, batchN02703MinusP029Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchN02703MinusP029DerivativeError2558 :
    ‖weightedUnitJet2539 3 (-1/2) nodeModulation2541 ⟨29, by omega⟩ batchN02703MinusPosition2558 -
      embedPair2542 batchN02703MinusP029Factor2558 * embedPair2542 batchN02703MinusP029Center2558‖
          ≤
        (pairMagnitude2542 batchN02703MinusP029Factor2558 : ℝ) * batchN02703MinusP029Error2558 :=
            by
  have hx : |batchN02703MinusPosition2558| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchN02703MinusPosition2558, storedWidth]
  have hf : weightedMultiplier2543 3 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchN02703MinusPosition2558 = embedPair2542
          batchN02703MinusP029Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchN02703MinusPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchN02703MinusP029Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchN02703MinusP029BaseError2558
    (embedPair_magnitude2542 batchN02703MinusP029Factor2558)

theorem batchN02703MinusGrid2558 :
    -stripRadius2303 + (2703 : ℝ) * (2 * stripRadius2303 / 10240) =
      batchN02703MinusPosition2558 := by
  norm_num [stripRadius2303, batchN02703MinusPosition2558]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchN02703MinusP000DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP001DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP002DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP003DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP004DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP005DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP006DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP007DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP008DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP009DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP010DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP011DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP012DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP013DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP014DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP015DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP016DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP017DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP018DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP019DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP020DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP021DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP022DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP023DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP024DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP025DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP026DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP027DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP028DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusP029DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchN02703MinusGrid2558
