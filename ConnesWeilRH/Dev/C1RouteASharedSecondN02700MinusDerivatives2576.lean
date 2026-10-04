import ConnesWeilRH.Dev.C1RouteAKernelN02700Minus2555

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def sharedSecondN02700MinusPointPosition2576 : ℝ := (((-7929856121) : ℝ) /
        2560000000)

theorem sharedSecondN02700MinusPointZero2576 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def sharedSecondN02700MinusPointP000Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP000Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP000Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP000Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP000Exterior2555 n

theorem sharedSecondN02700MinusPointP000BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP000Center2576‖ ≤
          sharedSecondN02700MinusPointP000Error2576 := by
  exact kernelN02700MinusP000BaseError2555

theorem sharedSecondN02700MinusPointP000DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP000Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP000Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP000Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP000Error2576 := by
  rw [sharedSecondN02700MinusPointP000Exterior2576]
  norm_num [sharedSecondN02700MinusPointP000Factor2576,
      sharedSecondN02700MinusPointP000Center2576,
      sharedSecondN02700MinusPointP000Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP001Input2576 : RatPair2542 :=
    ((((-(6688580688215936326964223499725723768788 *
    10^40
        + 4982692854096728503187522064213490083519)) : ℚ) /
        ((1 * 10^40
        + 8752578370474248106975932892819564741070) * 10^40
        + 9992275832742435204355224137891840000000)),
    ((43806833004475480685705509 : ℚ) /
        184467440737095516160000000))

def sharedSecondN02700MinusPointP001Center2576 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def sharedSecondN02700MinusPointP001Factor2576 : RatPair2542 :=
    ((((((((((19035286588674256370938333
    * 10^40
        + 678424616599432851065755647056987401843) * 10^40
        + 1538547041769087160039490661984195853971) * 10^40
        + 1634783791125258079123358390222750520876) * 10^40
        + 4842346408370980488323855746329852818030) * 10^40
        + 6343691297959943722150076677133682705857) * 10^40
        + 6895775867101691279220123974889717400113) * 10^40
        + 4430153541586352469694343967459298755255) : ℚ) /
        (((((((51868520597007919387 * 10^40
        + 5601122407350551953161243828772928082892) * 10^40
        + 2489956133954846109523637142872941443912) * 10^40
        + 3187203484236142584215364910637014360254) * 10^40
        + 9302592874709926532815021734195777928460) * 10^40
        + 1832600728856439219565652940133972215267) * 10^40
        + 7780311363481179019827186641049471457828) * 10^40
        + 1396340602638552730703884923081530015744)),
    (((-(((34520524014001664034815239457466903 * 10^40
        + 4480401662142748515170924645278679014182) * 10^40
        + 4834023515828287134853389447332777658264) * 10^40
        + 5298956530781237325468884182907081752291)) : ℚ) /
        (((720198032467514586083339390607 * 10^40
        + 1340073807940519252201462509517096295347) * 10^40
        + 184568515668281595107427435338868920201) * 10^40
        + 3006232590558185652464045229660950233088)))

noncomputable def sharedSecondN02700MinusPointP001Error2576 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem sharedSecondN02700MinusPointP001BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP001Center2576‖ ≤
          sharedSecondN02700MinusPointP001Error2576 := by
  exact kernelN02700MinusP001BaseError2555

theorem sharedSecondN02700MinusPointP001DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP001Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP001Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP001Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP001Error2576 := by
  have hx : |sharedSecondN02700MinusPointPosition2576| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [sharedSecondN02700MinusPointPosition2576, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) sharedSecondN02700MinusPointPosition2576 = embedPair2542
          sharedSecondN02700MinusPointP001Factor2576 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      sharedSecondN02700MinusPointPosition2576, storedWidth, nodeModulation2541, embedPair2542,
      sharedSecondN02700MinusPointP001Factor2576, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ sharedSecondN02700MinusPointP001BaseError2576
    (embedPair_magnitude2542 sharedSecondN02700MinusPointP001Factor2576)

def sharedSecondN02700MinusPointP002Input2576 : RatPair2542 := ((((-((17 * 10^40
        + 1805218828286032980113391054520037587918) * 10^40
        + 6926499854364897859155675096110909695679)) : ℚ) /
        ((73 * 10^40
        + 2973526485978139422317359752257065937823) * 10^40
        + 6716006270187613354841793103134720000000)),
    (((-43806833004475480685705509) : ℚ) /
        92233720368547758080000000))

def sharedSecondN02700MinusPointP002Center2576 : RatPair2542 := ((((-236687586501322481317) : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    (((-10235158114556736630683) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def sharedSecondN02700MinusPointP002Factor2576 : RatPair2542 :=
    ((((((((((183604661662432951517191113636 * 10^40
        + 3182906963560339176628703113418249969928) * 10^40
        + 4270582351644119679384926134463988701403) * 10^40
        + 160440295000816583578381353655139182376) * 10^40
        + 755979731026263943923144643290688329823) * 10^40
        + 4752523612612959301821867397582267058331) * 10^40
        + 9673752957381883886392233527782385677622) * 10^40
        + 6758677315978242729837759555761183376055) : ℚ) /
        (((((((1937015266588292515021073086 * 10^40
        + 2994542932171072373142020652603793467620) * 10^40
        + 517746388627032552464963942195336667049) * 10^40
        + 591194937561603428553392264434622954640) * 10^40
        + 7068096481983407493218124397848581437156) * 10^40
        + 809718152484384479355057324574717184699) * 10^40
        + 6713941467041095796487384540806101763070) * 10^40
        + 7825632187102251218431055071151111798784)),
    (((((14270160413854249379267819209254540808 * 10^40
        + 1536950840623272807450937198752191520629) * 10^40
        + 2836185249195339949790289392923579584079) * 10^40
        + 7994184099128538004048357380334754758371) : ℚ) /
        (((4401153560815951028705409995027431 * 10^40
        + 6407248073435955223846236977552315171045) * 10^40
        + 8283813287631791326751940695399995733594) * 10^40
        + 9087942328628108868562234793203259670528)))

noncomputable def sharedSecondN02700MinusPointP002Error2576 : ℝ := ((23242280564835055193 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem sharedSecondN02700MinusPointP002BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP002Center2576‖ ≤
          sharedSecondN02700MinusPointP002Error2576 := by
  exact kernelN02700MinusP002BaseError2555

theorem sharedSecondN02700MinusPointP002DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP002Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP002Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP002Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP002Error2576 := by
  have hx : |sharedSecondN02700MinusPointPosition2576| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [sharedSecondN02700MinusPointPosition2576, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) sharedSecondN02700MinusPointPosition2576 = embedPair2542
          sharedSecondN02700MinusPointP002Factor2576 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      sharedSecondN02700MinusPointPosition2576, storedWidth, nodeModulation2541, embedPair2542,
      sharedSecondN02700MinusPointP002Factor2576, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ sharedSecondN02700MinusPointP002BaseError2576
    (embedPair_magnitude2542 sharedSecondN02700MinusPointP002Factor2576)

def sharedSecondN02700MinusPointP003Input2576 : RatPair2542 := ((((-((2247 * 10^40
        + 2994581517147963196032705765199078519641) * 10^40
        + 1994410414746225504961591598744160567733)) : ℚ) /
        ((13284 * 10^40
        + 922703065279921881810676711054660831348) * 10^40
        + 9952512674799299317166344800829440000000)),
    (((-43806833004475480685705509) : ℚ) /
        92233720368547758080000000))

def sharedSecondN02700MinusPointP003Center2576 : RatPair2542 :=
    ((((-67562655288918125376430023877)
    : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-45650528571176392534168394947) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def sharedSecondN02700MinusPointP003Factor2576 : RatPair2542 :=
    ((((-(((((((8544796278133549807409673815848972403954 *
    10^40
        + 5148780304746974702236296744326117966943) * 10^40
        + 9346124922385846213563554774746441012444) * 10^40
        + 2213357598520455565336129140147330748050) * 10^40
        + 4060562948380167008157280037427345509031) * 10^40
        + 4661093304579241642837792047344323615308) * 10^40
        + 9480376989279185352952068834043345026810) * 10^40
        + 5173005475749556751906204012706785056235)) : ℚ) /
        (((((((6269438925985496490470165415362246911 * 10^40
        + 3986351596198586213858162653131823364356) * 10^40
        + 4884786397945068137126321303513742146538) * 10^40
        + 6057627864708420293925943004649441451063) * 10^40
        + 320148344534889669947883062501641901620) * 10^40
        + 4948917009426064438224771235840270595131) * 10^40
        + 3617210235859522895435880416922846300244) * 10^40
        + 3635566918499781850432845475919148613632)),
    ((((((47 * 10^40
        + 1305396224207851887726760680626273862936) * 10^40
        + 4288503688058138850570371905482038744634) * 10^40
        + 8325297562849717145432306889517235006661) * 10^40
        + 6522571712007595900708091926302181924577) : ℚ) /
        (((433685563259332964753142331202310329898 * 10^40
        + 6298521757412668391559923508799830282138) * 10^40
        + 4311430177896010460186375338656582973615) * 10^40
        + 5463602598314502655495224322941922574336)))

noncomputable def sharedSecondN02700MinusPointP003Error2576 : ℝ := ((48559493963991329543302431 :
    ℝ)
    /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336))

theorem sharedSecondN02700MinusPointP003BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP003Center2576‖ ≤
          sharedSecondN02700MinusPointP003Error2576 := by
  exact kernelN02700MinusP003BaseError2555

theorem sharedSecondN02700MinusPointP003DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP003Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP003Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP003Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP003Error2576 := by
  have hx : |sharedSecondN02700MinusPointPosition2576| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [sharedSecondN02700MinusPointPosition2576, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) sharedSecondN02700MinusPointPosition2576 = embedPair2542
          sharedSecondN02700MinusPointP003Factor2576 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      sharedSecondN02700MinusPointPosition2576, storedWidth, nodeModulation2541, embedPair2542,
      sharedSecondN02700MinusPointP003Factor2576, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ sharedSecondN02700MinusPointP003BaseError2576
    (embedPair_magnitude2542 sharedSecondN02700MinusPointP003Factor2576)

def sharedSecondN02700MinusPointP004Input2576 : RatPair2542 := ((((-((38 * 10^40
        + 8185595921673939082042460559705933328710) * 10^40
        + 152439585550817995883152104899972195679)) : ℚ) /
        ((267 * 10^40
        + 9934518708431604868451190036789843840469) * 10^40
        + 7242920599205959594841793103134720000000)),
    ((43806833004475480685705509 : ℚ) /
        92233720368547758080000000))

def sharedSecondN02700MinusPointP004Center2576 : RatPair2542 :=
    ((((-68389271845661481738864442245855) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((92418108643056889386327940952689 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def sharedSecondN02700MinusPointP004Factor2576 : RatPair2542 :=
    ((((-(((((((519648086629056483564668470070725 *
    10^40
        + 3508287247440087333820224239733716138167) * 10^40
        + 2680016625675954521466069662983505343031) * 10^40
        + 3418183225086706530554767681858676316533) * 10^40
        + 4745980545556695140522331711951016479438) * 10^40
        + 9884733111043178579585511637483575029961) * 10^40
        + 8207410322261943479741946305012105803902) * 10^40
        + 9021399469723893214315787065332566623945)) : ℚ) /
        (((((((346159789295829554768226901792 * 10^40
        + 5877373490737115164470290090017324813785) * 10^40
        + 3146519774778114397260837251212718051291) * 10^40
        + 958270215166616608804943199758833241743) * 10^40
        + 904824592855047867378029456509721945900) * 10^40
        + 3711706905336647286683410028339944102389) * 10^40
        + 8240546549958554745202121282503792516616) * 10^40
        + 2995293350786882591321167071151111798784)),
    (((-(((30831249046809951869141599791042878369 * 10^40
        + 4841346405359661604425161209785734855046) * 10^40
        + 3086295251703380283773077057878820910752) * 10^40
        + 8359323715502410044745514983850379758371)) : ℚ) /
        (((58835345609236422226412123959558397 * 10^40
        + 4662222656681608186279847456853005310927) * 10^40
        + 2074695575344593234733832197803294753423) * 10^40
        + 502235210582404750748986793203259670528)))

noncomputable def sharedSecondN02700MinusPointP004Error2576 : ℝ :=
    ((383779637246708834189989500561
    : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem sharedSecondN02700MinusPointP004BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP004Center2576‖ ≤
          sharedSecondN02700MinusPointP004Error2576 := by
  exact kernelN02700MinusP004BaseError2555

theorem sharedSecondN02700MinusPointP004DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP004Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP004Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP004Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP004Error2576 := by
  have hx : |sharedSecondN02700MinusPointPosition2576| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [sharedSecondN02700MinusPointPosition2576, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) sharedSecondN02700MinusPointPosition2576 = embedPair2542
          sharedSecondN02700MinusPointP004Factor2576 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      sharedSecondN02700MinusPointPosition2576, storedWidth, nodeModulation2541, embedPair2542,
      sharedSecondN02700MinusPointP004Factor2576, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ sharedSecondN02700MinusPointP004BaseError2576
    (embedPair_magnitude2542 sharedSecondN02700MinusPointP004Factor2576)

def sharedSecondN02700MinusPointP005Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP005Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP005Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP005Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP005Exterior2555 n

theorem sharedSecondN02700MinusPointP005BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP005Center2576‖ ≤
          sharedSecondN02700MinusPointP005Error2576 := by
  exact kernelN02700MinusP005BaseError2555

theorem sharedSecondN02700MinusPointP005DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP005Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP005Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP005Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP005Error2576 := by
  rw [sharedSecondN02700MinusPointP005Exterior2576]
  norm_num [sharedSecondN02700MinusPointP005Factor2576,
      sharedSecondN02700MinusPointP005Center2576,
      sharedSecondN02700MinusPointP005Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP006Input2576 : RatPair2542 :=
    ((((-5257757264283175625308744953187)
    : ℚ) /
        9169574712713507276718080000000),
    ((0 : ℚ) /
        1))

def sharedSecondN02700MinusPointP006Center2576 : RatPair2542 := (((19504508082407141 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def sharedSecondN02700MinusPointP006Factor2576 : RatPair2542 := (((((7 * 10^40
        + 6938224811455683724817971110072149172489) * 10^40
        + 4590681357598535924590867176766091085681) : ℚ) /
        (15329819545931485874815025817712402547 * 10^40
        + 8017962395195720658363468707064364342724)),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP006Error2576 : ℝ := ((7069434267121 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem sharedSecondN02700MinusPointP006BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP006Center2576‖ ≤
          sharedSecondN02700MinusPointP006Error2576 := by
  exact kernelN02700MinusP006BaseError2555

theorem sharedSecondN02700MinusPointP006DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP006Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP006Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP006Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP006Error2576 := by
  have hx : |sharedSecondN02700MinusPointPosition2576| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [sharedSecondN02700MinusPointPosition2576, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) sharedSecondN02700MinusPointPosition2576 = embedPair2542
          sharedSecondN02700MinusPointP006Factor2576 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      sharedSecondN02700MinusPointPosition2576, storedWidth, nodeModulation2541, embedPair2542,
      sharedSecondN02700MinusPointP006Factor2576, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ sharedSecondN02700MinusPointP006BaseError2576
    (embedPair_magnitude2542 sharedSecondN02700MinusPointP006Factor2576)

def sharedSecondN02700MinusPointP007Input2576 : RatPair2542 := ((((-((2247 * 10^40
        + 2994581517147963196032705765199078519641) * 10^40
        + 1994410414746225504961591598744160567733)) : ℚ) /
        ((3321 * 10^40
        + 230675766319980470452669177763665207837) * 10^40
        + 2488128168699824829291586200207360000000)),
    ((0 : ℚ) /
        1))

def sharedSecondN02700MinusPointP007Center2576 : RatPair2542 := (((227161576196330745979291438463
    :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def sharedSecondN02700MinusPointP007Factor2576 : RatPair2542 := ((((((((((225146473814 * 10^40
        + 6230637970652174986573313554132054850742) * 10^40
        + 1309900348754636593190099713892322829180) * 10^40
        + 7516169052190360901108617193747344540209) * 10^40
        + 4136144654374529785559653521605126072135) * 10^40
        + 2340011005329303853007971497095413754948) * 10^40
        + 4522000104750172583736059263080123297576) * 10^40
        + 3307218585294203111652506922112238686323) : ℚ) /
        (((((((1266103108 * 10^40
        + 1934762993400938604457984602462360931930) * 10^40
        + 5880934758063205803506445443404815325672) * 10^40
        + 9101605719657091712027095092488838501478) * 10^40
        + 8197330286653926140330115552242395289312) * 10^40
        + 9552340670800492404516763478302994173772) * 10^40
        + 832533828333531988763241620710797271128) * 10^40
        + 8183659109176812446610027688448954745292)),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP007Error2576 : ℝ := ((31448282402248334335030421 :
    ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem sharedSecondN02700MinusPointP007BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP007Center2576‖ ≤
          sharedSecondN02700MinusPointP007Error2576 := by
  exact kernelN02700MinusP007BaseError2555

theorem sharedSecondN02700MinusPointP007DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP007Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP007Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP007Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP007Error2576 := by
  have hx : |sharedSecondN02700MinusPointPosition2576| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [sharedSecondN02700MinusPointPosition2576, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) sharedSecondN02700MinusPointPosition2576 = embedPair2542
          sharedSecondN02700MinusPointP007Factor2576 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      sharedSecondN02700MinusPointPosition2576, storedWidth, nodeModulation2541, embedPair2542,
      sharedSecondN02700MinusPointP007Factor2576, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ sharedSecondN02700MinusPointP007BaseError2576
    (embedPair_magnitude2542 sharedSecondN02700MinusPointP007Factor2576)

def sharedSecondN02700MinusPointP008Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP008Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP008Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP008Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP008Exterior2555 n

theorem sharedSecondN02700MinusPointP008BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP008Center2576‖ ≤
          sharedSecondN02700MinusPointP008Error2576 := by
  exact kernelN02700MinusP008BaseError2555

theorem sharedSecondN02700MinusPointP008DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP008Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP008Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP008Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP008Error2576 := by
  rw [sharedSecondN02700MinusPointP008Exterior2576]
  norm_num [sharedSecondN02700MinusPointP008Factor2576,
      sharedSecondN02700MinusPointP008Center2576,
      sharedSecondN02700MinusPointP008Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP009Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP009Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP009Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP009Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP009Exterior2555 n

theorem sharedSecondN02700MinusPointP009BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP009Center2576‖ ≤
          sharedSecondN02700MinusPointP009Error2576 := by
  exact kernelN02700MinusP009BaseError2555

theorem sharedSecondN02700MinusPointP009DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP009Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP009Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP009Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP009Error2576 := by
  rw [sharedSecondN02700MinusPointP009Exterior2576]
  norm_num [sharedSecondN02700MinusPointP009Factor2576,
      sharedSecondN02700MinusPointP009Center2576,
      sharedSecondN02700MinusPointP009Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP010Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP010Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP010Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP010Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP010Exterior2555 n

theorem sharedSecondN02700MinusPointP010BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP010Center2576‖ ≤
          sharedSecondN02700MinusPointP010Error2576 := by
  exact kernelN02700MinusP010BaseError2555

theorem sharedSecondN02700MinusPointP010DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP010Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP010Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP010Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP010Error2576 := by
  rw [sharedSecondN02700MinusPointP010Exterior2576]
  norm_num [sharedSecondN02700MinusPointP010Factor2576,
      sharedSecondN02700MinusPointP010Center2576,
      sharedSecondN02700MinusPointP010Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP011Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP011Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP011Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP011Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP011Exterior2555 n

theorem sharedSecondN02700MinusPointP011BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP011Center2576‖ ≤
          sharedSecondN02700MinusPointP011Error2576 := by
  exact kernelN02700MinusP011BaseError2555

theorem sharedSecondN02700MinusPointP011DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP011Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP011Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP011Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP011Error2576 := by
  rw [sharedSecondN02700MinusPointP011Exterior2576]
  norm_num [sharedSecondN02700MinusPointP011Factor2576,
      sharedSecondN02700MinusPointP011Center2576,
      sharedSecondN02700MinusPointP011Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP012Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP012Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP012Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP012Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP012Exterior2555 n

theorem sharedSecondN02700MinusPointP012BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP012Center2576‖ ≤
          sharedSecondN02700MinusPointP012Error2576 := by
  exact kernelN02700MinusP012BaseError2555

theorem sharedSecondN02700MinusPointP012DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP012Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP012Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP012Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP012Error2576 := by
  rw [sharedSecondN02700MinusPointP012Exterior2576]
  norm_num [sharedSecondN02700MinusPointP012Factor2576,
      sharedSecondN02700MinusPointP012Center2576,
      sharedSecondN02700MinusPointP012Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP013Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP013Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP013Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP013Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP013Exterior2555 n

theorem sharedSecondN02700MinusPointP013BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP013Center2576‖ ≤
          sharedSecondN02700MinusPointP013Error2576 := by
  exact kernelN02700MinusP013BaseError2555

theorem sharedSecondN02700MinusPointP013DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP013Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP013Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP013Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP013Error2576 := by
  rw [sharedSecondN02700MinusPointP013Exterior2576]
  norm_num [sharedSecondN02700MinusPointP013Factor2576,
      sharedSecondN02700MinusPointP013Center2576,
      sharedSecondN02700MinusPointP013Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP014Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP014Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP014Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP014Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP014Exterior2555 n

theorem sharedSecondN02700MinusPointP014BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP014Center2576‖ ≤
          sharedSecondN02700MinusPointP014Error2576 := by
  exact kernelN02700MinusP014BaseError2555

theorem sharedSecondN02700MinusPointP014DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP014Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP014Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP014Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP014Error2576 := by
  rw [sharedSecondN02700MinusPointP014Exterior2576]
  norm_num [sharedSecondN02700MinusPointP014Factor2576,
      sharedSecondN02700MinusPointP014Center2576,
      sharedSecondN02700MinusPointP014Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP015Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP015Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP015Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP015Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP015Exterior2555 n

theorem sharedSecondN02700MinusPointP015BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP015Center2576‖ ≤
          sharedSecondN02700MinusPointP015Error2576 := by
  exact kernelN02700MinusP015BaseError2555

theorem sharedSecondN02700MinusPointP015DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP015Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP015Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP015Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP015Error2576 := by
  rw [sharedSecondN02700MinusPointP015Exterior2576]
  norm_num [sharedSecondN02700MinusPointP015Factor2576,
      sharedSecondN02700MinusPointP015Center2576,
      sharedSecondN02700MinusPointP015Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP016Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP016Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP016Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP016Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP016Exterior2555 n

theorem sharedSecondN02700MinusPointP016BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP016Center2576‖ ≤
          sharedSecondN02700MinusPointP016Error2576 := by
  exact kernelN02700MinusP016BaseError2555

theorem sharedSecondN02700MinusPointP016DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP016Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP016Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP016Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP016Error2576 := by
  rw [sharedSecondN02700MinusPointP016Exterior2576]
  norm_num [sharedSecondN02700MinusPointP016Factor2576,
      sharedSecondN02700MinusPointP016Center2576,
      sharedSecondN02700MinusPointP016Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP017Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP017Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP017Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP017Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP017Exterior2555 n

theorem sharedSecondN02700MinusPointP017BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP017Center2576‖ ≤
          sharedSecondN02700MinusPointP017Error2576 := by
  exact kernelN02700MinusP017BaseError2555

theorem sharedSecondN02700MinusPointP017DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP017Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP017Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP017Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP017Error2576 := by
  rw [sharedSecondN02700MinusPointP017Exterior2576]
  norm_num [sharedSecondN02700MinusPointP017Factor2576,
      sharedSecondN02700MinusPointP017Center2576,
      sharedSecondN02700MinusPointP017Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP018Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP018Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP018Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP018Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP018Exterior2555 n

theorem sharedSecondN02700MinusPointP018BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP018Center2576‖ ≤
          sharedSecondN02700MinusPointP018Error2576 := by
  exact kernelN02700MinusP018BaseError2555

theorem sharedSecondN02700MinusPointP018DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP018Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP018Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP018Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP018Error2576 := by
  rw [sharedSecondN02700MinusPointP018Exterior2576]
  norm_num [sharedSecondN02700MinusPointP018Factor2576,
      sharedSecondN02700MinusPointP018Center2576,
      sharedSecondN02700MinusPointP018Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP019Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP019Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP019Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP019Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP019Exterior2555 n

theorem sharedSecondN02700MinusPointP019BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP019Center2576‖ ≤
          sharedSecondN02700MinusPointP019Error2576 := by
  exact kernelN02700MinusP019BaseError2555

theorem sharedSecondN02700MinusPointP019DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP019Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP019Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP019Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP019Error2576 := by
  rw [sharedSecondN02700MinusPointP019Exterior2576]
  norm_num [sharedSecondN02700MinusPointP019Factor2576,
      sharedSecondN02700MinusPointP019Center2576,
      sharedSecondN02700MinusPointP019Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP020Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP020Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP020Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP020Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP020Exterior2555 n

theorem sharedSecondN02700MinusPointP020BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP020Center2576‖ ≤
          sharedSecondN02700MinusPointP020Error2576 := by
  exact kernelN02700MinusP020BaseError2555

theorem sharedSecondN02700MinusPointP020DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP020Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP020Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP020Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP020Error2576 := by
  rw [sharedSecondN02700MinusPointP020Exterior2576]
  norm_num [sharedSecondN02700MinusPointP020Factor2576,
      sharedSecondN02700MinusPointP020Center2576,
      sharedSecondN02700MinusPointP020Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP021Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP021Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP021Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP021Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP021Exterior2555 n

theorem sharedSecondN02700MinusPointP021BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP021Center2576‖ ≤
          sharedSecondN02700MinusPointP021Error2576 := by
  exact kernelN02700MinusP021BaseError2555

theorem sharedSecondN02700MinusPointP021DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP021Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP021Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP021Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP021Error2576 := by
  rw [sharedSecondN02700MinusPointP021Exterior2576]
  norm_num [sharedSecondN02700MinusPointP021Factor2576,
      sharedSecondN02700MinusPointP021Center2576,
      sharedSecondN02700MinusPointP021Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP022Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP022Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP022Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP022Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP022Exterior2555 n

theorem sharedSecondN02700MinusPointP022BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP022Center2576‖ ≤
          sharedSecondN02700MinusPointP022Error2576 := by
  exact kernelN02700MinusP022BaseError2555

theorem sharedSecondN02700MinusPointP022DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP022Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP022Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP022Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP022Error2576 := by
  rw [sharedSecondN02700MinusPointP022Exterior2576]
  norm_num [sharedSecondN02700MinusPointP022Factor2576,
      sharedSecondN02700MinusPointP022Center2576,
      sharedSecondN02700MinusPointP022Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP023Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP023Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP023Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP023Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP023Exterior2555 n

theorem sharedSecondN02700MinusPointP023BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP023Center2576‖ ≤
          sharedSecondN02700MinusPointP023Error2576 := by
  exact kernelN02700MinusP023BaseError2555

theorem sharedSecondN02700MinusPointP023DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP023Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP023Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP023Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP023Error2576 := by
  rw [sharedSecondN02700MinusPointP023Exterior2576]
  norm_num [sharedSecondN02700MinusPointP023Factor2576,
      sharedSecondN02700MinusPointP023Center2576,
      sharedSecondN02700MinusPointP023Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP024Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP024Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP024Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP024Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP024Exterior2555 n

theorem sharedSecondN02700MinusPointP024BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP024Center2576‖ ≤
          sharedSecondN02700MinusPointP024Error2576 := by
  exact kernelN02700MinusP024BaseError2555

theorem sharedSecondN02700MinusPointP024DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP024Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP024Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP024Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP024Error2576 := by
  rw [sharedSecondN02700MinusPointP024Exterior2576]
  norm_num [sharedSecondN02700MinusPointP024Factor2576,
      sharedSecondN02700MinusPointP024Center2576,
      sharedSecondN02700MinusPointP024Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP025Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP025Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP025Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP025Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP025Exterior2555 n

theorem sharedSecondN02700MinusPointP025BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP025Center2576‖ ≤
          sharedSecondN02700MinusPointP025Error2576 := by
  exact kernelN02700MinusP025BaseError2555

theorem sharedSecondN02700MinusPointP025DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP025Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP025Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP025Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP025Error2576 := by
  rw [sharedSecondN02700MinusPointP025Exterior2576]
  norm_num [sharedSecondN02700MinusPointP025Factor2576,
      sharedSecondN02700MinusPointP025Center2576,
      sharedSecondN02700MinusPointP025Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP026Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP026Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP026Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP026Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP026Exterior2555 n

theorem sharedSecondN02700MinusPointP026BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP026Center2576‖ ≤
          sharedSecondN02700MinusPointP026Error2576 := by
  exact kernelN02700MinusP026BaseError2555

theorem sharedSecondN02700MinusPointP026DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP026Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP026Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP026Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP026Error2576 := by
  rw [sharedSecondN02700MinusPointP026Exterior2576]
  norm_num [sharedSecondN02700MinusPointP026Factor2576,
      sharedSecondN02700MinusPointP026Center2576,
      sharedSecondN02700MinusPointP026Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP027Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP027Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP027Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP027Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP027Exterior2555 n

theorem sharedSecondN02700MinusPointP027BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP027Center2576‖ ≤
          sharedSecondN02700MinusPointP027Error2576 := by
  exact kernelN02700MinusP027BaseError2555

theorem sharedSecondN02700MinusPointP027DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP027Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP027Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP027Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP027Error2576 := by
  rw [sharedSecondN02700MinusPointP027Exterior2576]
  norm_num [sharedSecondN02700MinusPointP027Factor2576,
      sharedSecondN02700MinusPointP027Center2576,
      sharedSecondN02700MinusPointP027Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP028Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP028Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP028Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP028Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP028Exterior2555 n

theorem sharedSecondN02700MinusPointP028BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP028Center2576‖ ≤
          sharedSecondN02700MinusPointP028Error2576 := by
  exact kernelN02700MinusP028BaseError2555

theorem sharedSecondN02700MinusPointP028DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP028Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP028Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP028Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP028Error2576 := by
  rw [sharedSecondN02700MinusPointP028Exterior2576]
  norm_num [sharedSecondN02700MinusPointP028Factor2576,
      sharedSecondN02700MinusPointP028Center2576,
      sharedSecondN02700MinusPointP028Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

def sharedSecondN02700MinusPointP029Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700MinusPointP029Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700MinusPointP029Error2576 : ℝ := 0

theorem sharedSecondN02700MinusPointP029Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02700MinusPointPosition2576 = 0 := by
  exact kernelN02700MinusP029Exterior2555 n

theorem sharedSecondN02700MinusPointP029BaseError2576 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP029Center2576‖ ≤
          sharedSecondN02700MinusPointP029Error2576 := by
  exact kernelN02700MinusP029BaseError2555

theorem sharedSecondN02700MinusPointP029DerivativeError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP029Factor2576 * embedPair2542
          sharedSecondN02700MinusPointP029Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700MinusPointP029Factor2576 : ℝ) *
            sharedSecondN02700MinusPointP029Error2576 := by
  rw [sharedSecondN02700MinusPointP029Exterior2576]
  norm_num [sharedSecondN02700MinusPointP029Factor2576,
      sharedSecondN02700MinusPointP029Center2576,
      sharedSecondN02700MinusPointP029Error2576,
      sharedSecondN02700MinusPointZero2576, pairMagnitude2542]

theorem sharedSecondN02700MinusPointGrid2576 :
    -stripRadius2303 + (2700 : ℝ) * (2 * stripRadius2303 / 10240) =
      sharedSecondN02700MinusPointPosition2576 := by
  norm_num [stripRadius2303, sharedSecondN02700MinusPointPosition2576]

end ConnesWeilRH.Dev
