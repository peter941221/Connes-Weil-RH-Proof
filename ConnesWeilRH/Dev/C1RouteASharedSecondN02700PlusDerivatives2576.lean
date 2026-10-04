import ConnesWeilRH.Dev.C1RouteAKernelN02700Plus2555

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def sharedSecondN02700PlusPointPosition2576 : ℝ := (((-7929856121) : ℝ) /
        2560000000)

theorem sharedSecondN02700PlusPointZero2576 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def sharedSecondN02700PlusPointP000Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP000Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP000Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP000Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP000Exterior2555 n

theorem sharedSecondN02700PlusPointP000BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP000Center2576‖ ≤
          sharedSecondN02700PlusPointP000Error2576 := by
  exact kernelN02700PlusP000BaseError2555

theorem sharedSecondN02700PlusPointP000DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP000Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP000Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP000Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP000Error2576 := by
  rw [sharedSecondN02700PlusPointP000Exterior2576]
  norm_num [sharedSecondN02700PlusPointP000Factor2576, sharedSecondN02700PlusPointP000Center2576,
      sharedSecondN02700PlusPointP000Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP001Input2576 : RatPair2542 :=
    ((((-(6802033789088462436296480399940728088864 *
    10^40
        + 8972281175305676998687477935786509916481)) : ℚ) /
        ((1 * 10^40
        + 8752578370474248106975932892819564741070) * 10^40
        + 9992275832742435204355224137891840000000)),
    ((43806833004475480685705509 : ℚ) /
        184467440737095516160000000))

def sharedSecondN02700PlusPointP001Center2576 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def sharedSecondN02700PlusPointP001Factor2576 : RatPair2542 :=
    ((((((((((19098676196292801162865582
    * 10^40
        + 7213145833202522019965882648034404158734) * 10^40
        + 3863537911283844023526122557908036882175) * 10^40
        + 6409686887851301731728069997996278120800) * 10^40
        + 513888277525927322321556141461843585467) * 10^40
        + 6267523003856335731097560790375379026608) * 10^40
        + 9168147330473453534803984223051799417455) * 10^40
        + 7105130479015262549694343967459298755255) : ℚ) /
        (((((((51868520597007919387 * 10^40
        + 5601122407350551953161243828772928082892) * 10^40
        + 2489956133954846109523637142872941443912) * 10^40
        + 3187203484236142584215364910637014360254) * 10^40
        + 9302592874709926532815021734195777928460) * 10^40
        + 1832600728856439219565652940133972215267) * 10^40
        + 7780311363481179019827186641049471457828) * 10^40
        + 1396340602638552730703884923081530015744)),
    (((-(((34577063086483263460998553433837698 * 10^40
        + 1221543352717869448175436504932199015318) * 10^40
        + 9464897739776860121147227323674069340635) * 10^40
        + 8919998751218880434531115817092918247709)) : ℚ) /
        (((720198032467514586083339390607 * 10^40
        + 1340073807940519252201462509517096295347) * 10^40
        + 184568515668281595107427435338868920201) * 10^40
        + 3006232590558185652464045229660950233088)))

noncomputable def sharedSecondN02700PlusPointP001Error2576 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem sharedSecondN02700PlusPointP001BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP001Center2576‖ ≤
          sharedSecondN02700PlusPointP001Error2576 := by
  exact kernelN02700PlusP001BaseError2555

theorem sharedSecondN02700PlusPointP001DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP001Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP001Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP001Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP001Error2576 := by
  have hx : |sharedSecondN02700PlusPointPosition2576| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [sharedSecondN02700PlusPointPosition2576, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) sharedSecondN02700PlusPointPosition2576 = embedPair2542
          sharedSecondN02700PlusPointP001Factor2576 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      sharedSecondN02700PlusPointPosition2576, storedWidth, nodeModulation2541, embedPair2542,
      sharedSecondN02700PlusPointP001Factor2576, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ sharedSecondN02700PlusPointP001BaseError2576
    (embedPair_magnitude2542 sharedSecondN02700PlusPointP001Factor2576)

def sharedSecondN02700PlusPointP002Input2576 : RatPair2542 := ((((-((18 * 10^40
        + 674198634096258458583628358041758074204) * 10^40
        + 9347881399256746042719324903889090304321)) : ℚ) /
        ((73 * 10^40
        + 2973526485978139422317359752257065937823) * 10^40
        + 6716006270187613354841793103134720000000)),
    (((-43806833004475480685705509) : ℚ) /
        92233720368547758080000000))

def sharedSecondN02700PlusPointP002Center2576 : RatPair2542 := ((((-342022637592315929245) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-462193622279321905361) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def sharedSecondN02700PlusPointP002Factor2576 : RatPair2542 :=
    ((((((((((345544860379012142879627721976 * 10^40
        + 5422514320504338937289060576791240845785) * 10^40
        + 8043399267269685315342511059489863230918) * 10^40
        + 3291086337740541799890037146090993847883) * 10^40
        + 3518460486988500146828939833525334536012) * 10^40
        + 9413317329659070553573053570238154495084) * 10^40
        + 5368775356746945369345053766218203853273) * 10^40
        + 3345131110419376809837759555761183376055) : ℚ) /
        (((((((1937015266588292515021073086 * 10^40
        + 2994542932171072373142020652603793467620) * 10^40
        + 517746388627032552464963942195336667049) * 10^40
        + 591194937561603428553392264434622954640) * 10^40
        + 7068096481983407493218124397848581437156) * 10^40
        + 809718152484384479355057324574717184699) * 10^40
        + 6713941467041095796487384540806101763070) * 10^40
        + 7825632187102251218431055071151111798784)),
    (((((14615672521579768009071548382823645753 * 10^40
        + 1274915251756183935966473667640801880451) * 10^40
        + 7472630107573189678566371928566826450920) * 10^40
        + 1023080178186062955951642619665245241629) : ℚ) /
        (((4401153560815951028705409995027431 * 10^40
        + 6407248073435955223846236977552315171045) * 10^40
        + 8283813287631791326751940695399995733594) * 10^40
        + 9087942328628108868562234793203259670528)))

noncomputable def sharedSecondN02700PlusPointP002Error2576 : ℝ := ((2124679950171895707 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem sharedSecondN02700PlusPointP002BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP002Center2576‖ ≤
          sharedSecondN02700PlusPointP002Error2576 := by
  exact kernelN02700PlusP002BaseError2555

theorem sharedSecondN02700PlusPointP002DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP002Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP002Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP002Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP002Error2576 := by
  have hx : |sharedSecondN02700PlusPointPosition2576| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [sharedSecondN02700PlusPointPosition2576, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) sharedSecondN02700PlusPointPosition2576 = embedPair2542
          sharedSecondN02700PlusPointP002Factor2576 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      sharedSecondN02700PlusPointPosition2576, storedWidth, nodeModulation2541, embedPair2542,
      sharedSecondN02700PlusPointP002Factor2576, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ sharedSecondN02700PlusPointP002BaseError2576
    (embedPair_magnitude2542 sharedSecondN02700PlusPointP002Factor2576)

def sharedSecondN02700PlusPointP003Input2576 : RatPair2542 := ((((-((2408 * 10^40
        + 369770750836432817481799749086268690782) * 10^40
        + 3306951315371206135663408401255839432267)) : ℚ) /
        ((13284 * 10^40
        + 922703065279921881810676711054660831348) * 10^40
        + 9952512674799299317166344800829440000000)),
    (((-43806833004475480685705509) : ℚ) /
        92233720368547758080000000))

def sharedSecondN02700PlusPointP003Center2576 : RatPair2542 := ((((-3050957105819623379802289723)
    :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-4122922757640557388486708103) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def sharedSecondN02700PlusPointP003Factor2576 : RatPair2542 :=
    ((((-(((((((2788316987232691581956928599671085251719 *
    10^40
        + 1550172693336437341894637354526360444879) * 10^40
        + 9327643610214914422664429116768398982509) * 10^40
        + 2710009956175430050696867167446756074874) * 10^40
        + 4644332498240689065468504597227638111904) * 10^40
        + 5446753652663101395044377574783886945445) * 10^40
        + 7087946107402158024572724732472257581708) * 10^40
        + 8274321803916518917302068004235595018745)) : ℚ) /
        (((((((2089812975328498830156721805120748970 * 10^40
        + 4662117198732862071286054217710607788118) * 10^40
        + 8294928799315022712375440434504580715512) * 10^40
        + 8685875954902806764641981001549813817021) * 10^40
        + 106716114844963223315961020833880633873) * 10^40
        + 4982972336475354812741590411946756865043) * 10^40
        + 7872403411953174298478626805640948766748) * 10^40
        + 1211855639499927283477615158639716204544)),
    ((((((50 * 10^40
        + 5351836772417364372657091169892534087925) * 10^40
        + 7064680823247389367854992730459906645640) * 10^40
        + 9722136319454892688493096743272584224985) * 10^40
        + 5122210879992404099291908073697818075423) : ℚ) /
        (((433685563259332964753142331202310329898 * 10^40
        + 6298521757412668391559923508799830282138) * 10^40
        + 4311430177896010460186375338656582973615) * 10^40
        + 5463602598314502655495224322941922574336)))

noncomputable def sharedSecondN02700PlusPointP003Error2576 : ℝ := ((35512274632534440194531833 :
    ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem sharedSecondN02700PlusPointP003BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP003Center2576‖ ≤
          sharedSecondN02700PlusPointP003Error2576 := by
  exact kernelN02700PlusP003BaseError2555

theorem sharedSecondN02700PlusPointP003DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP003Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP003Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP003Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP003Error2576 := by
  have hx : |sharedSecondN02700PlusPointPosition2576| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [sharedSecondN02700PlusPointPosition2576, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) sharedSecondN02700PlusPointPosition2576 = embedPair2542
          sharedSecondN02700PlusPointP003Factor2576 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      sharedSecondN02700PlusPointPosition2576, storedWidth, nodeModulation2541, embedPair2542,
      sharedSecondN02700PlusPointP003Factor2576, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ sharedSecondN02700PlusPointP003BaseError2576
    (embedPair_magnitude2542 sharedSecondN02700PlusPointP003Factor2576)

def sharedSecondN02700PlusPointP004Input2576 : RatPair2542 := ((((-((42 * 10^40
        + 612804092845883320592175325793232154346) * 10^40
        + 2807937213934500805991847895100027804321)) : ℚ) /
        ((267 * 10^40
        + 9934518708431604868451190036789843840469) * 10^40
        + 7242920599205959594841793103134720000000)),
    ((43806833004475480685705509 : ℚ) /
        92233720368547758080000000))

def sharedSecondN02700PlusPointP004Center2576 : RatPair2542 :=
    ((((-3088285000154142764160101575539)
    : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((4173365952909685099392742956493 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def sharedSecondN02700PlusPointP004Factor2576 : RatPair2542 :=
    ((((-(((((((514680642668703333595397276009745 *
    10^40
        + 8090269532944563621184932110687013390374) * 10^40
        + 9752868890420173181327392006506402109718) * 10^40
        + 4232763328410848948153112321146220173106) * 10^40
        + 3823154555327685899492594803653496271948) * 10^40
        + 475680540617270335561327921840114083747) * 10^40
        + 5404273138088331690576823875324294025848) * 10^40
        + 9174755089539808734315787065332566623945)) : ℚ) /
        (((((((346159789295829554768226901792 * 10^40
        + 5877373490737115164470290090017324813785) * 10^40
        + 3146519774778114397260837251212718051291) * 10^40
        + 958270215166616608804943199758833241743) * 10^40
        + 904824592855047867378029456509721945900) * 10^40
        + 3711706905336647286683410028339944102389) * 10^40
        + 8240546549958554745202121282503792516616) * 10^40
        + 2995293350786882591321167071151111798784)),
    (((-(((35450111803881724756100246874002939638 * 10^40
        + 9246668473660018337298115572298216379056) * 10^40
        + 3959107145580611144553057247291471512406) * 10^40
        + 8479740667504555715254485016149620241629)) : ℚ) /
        (((58835345609236422226412123959558397 * 10^40
        + 4662222656681608186279847456853005310927) * 10^40
        + 2074695575344593234733832197803294753423) * 10^40
        + 502235210582404750748986793203259670528)))

noncomputable def sharedSecondN02700PlusPointP004Error2576 : ℝ := ((4385370515285168518352942979 :
    ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem sharedSecondN02700PlusPointP004BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP004Center2576‖ ≤
          sharedSecondN02700PlusPointP004Error2576 := by
  exact kernelN02700PlusP004BaseError2555

theorem sharedSecondN02700PlusPointP004DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP004Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP004Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP004Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP004Error2576 := by
  have hx : |sharedSecondN02700PlusPointPosition2576| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [sharedSecondN02700PlusPointPosition2576, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) sharedSecondN02700PlusPointPosition2576 = embedPair2542
          sharedSecondN02700PlusPointP004Factor2576 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      sharedSecondN02700PlusPointPosition2576, storedWidth, nodeModulation2541, embedPair2542,
      sharedSecondN02700PlusPointP004Factor2576, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ sharedSecondN02700PlusPointP004BaseError2576
    (embedPair_magnitude2542 sharedSecondN02700PlusPointP004Factor2576)

def sharedSecondN02700PlusPointP005Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP005Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP005Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP005Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP005Exterior2555 n

theorem sharedSecondN02700PlusPointP005BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP005Center2576‖ ≤
          sharedSecondN02700PlusPointP005Error2576 := by
  exact kernelN02700PlusP005BaseError2555

theorem sharedSecondN02700PlusPointP005DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP005Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP005Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP005Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP005Error2576 := by
  rw [sharedSecondN02700PlusPointP005Exterior2576]
  norm_num [sharedSecondN02700PlusPointP005Factor2576, sharedSecondN02700PlusPointP005Center2576,
      sharedSecondN02700PlusPointP005Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP006Input2576 : RatPair2542 :=
    ((((-5479660975716824374691255046813)
    : ℚ) /
        9169574712713507276718080000000),
    ((0 : ℚ) /
        1))

def sharedSecondN02700PlusPointP006Center2576 : RatPair2542 := (((440386906605911 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def sharedSecondN02700PlusPointP006Factor2576 : RatPair2542 := (((((23 * 10^40
        + 7482184721994964803550087096845308858719) * 10^40
        + 3388444275197973213772601530298273257043) : ℚ) /
        (45989458637794457624445077453137207643 * 10^40
        + 4053887185587161975090406121193093028172)),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP006Error2576 : ℝ := ((2424345947741 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem sharedSecondN02700PlusPointP006BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP006Center2576‖ ≤
          sharedSecondN02700PlusPointP006Error2576 := by
  exact kernelN02700PlusP006BaseError2555

theorem sharedSecondN02700PlusPointP006DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP006Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP006Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP006Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP006Error2576 := by
  have hx : |sharedSecondN02700PlusPointPosition2576| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [sharedSecondN02700PlusPointPosition2576, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) sharedSecondN02700PlusPointPosition2576 = embedPair2542
          sharedSecondN02700PlusPointP006Factor2576 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      sharedSecondN02700PlusPointPosition2576, storedWidth, nodeModulation2541, embedPair2542,
      sharedSecondN02700PlusPointP006Factor2576, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ sharedSecondN02700PlusPointP006BaseError2576
    (embedPair_magnitude2542 sharedSecondN02700PlusPointP006Factor2576)

def sharedSecondN02700PlusPointP007Input2576 : RatPair2542 := ((((-((2408 * 10^40
        + 369770750836432817481799749086268690782) * 10^40
        + 3306951315371206135663408401255839432267)) : ℚ) /
        ((3321 * 10^40
        + 230675766319980470452669177763665207837) * 10^40
        + 2488128168699824829291586200207360000000)),
    ((0 : ℚ) /
        1))

def sharedSecondN02700PlusPointP007Center2576 : RatPair2542 := (((1282254638493795595923663161 :
    ℚ)
    /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1))

def sharedSecondN02700PlusPointP007Factor2576 : RatPair2542 := ((((((((((87155315410 * 10^40
        + 411317067120523094025755250592972698779) * 10^40
        + 7149651159700607054843975731674960668369) * 10^40
        + 1333158910719407430859552636024564080512) * 10^40
        + 207986715755790749007599535306353449151) * 10^40
        + 9825680055316201249366907174181924261975) * 10^40
        + 3483918076837184057630281929131694270184) * 10^40
        + 7834870323098067703884168974037412895441) : ℚ) /
        (((((((422034369 * 10^40
        + 3978254331133646201485994867487453643976) * 10^40
        + 8626978252687735267835481814468271775224) * 10^40
        + 3033868573219030570675698364162946167159) * 10^40
        + 6065776762217975380110038517414131763104) * 10^40
        + 3184113556933497468172254492767664724590) * 10^40
        + 6944177942777843996254413873570265757042) * 10^40
        + 9394553036392270815536675896149651581764)),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP007Error2576 : ℝ := ((372637180338657148206451 : ℝ)
    /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem sharedSecondN02700PlusPointP007BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP007Center2576‖ ≤
          sharedSecondN02700PlusPointP007Error2576 := by
  exact kernelN02700PlusP007BaseError2555

theorem sharedSecondN02700PlusPointP007DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP007Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP007Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP007Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP007Error2576 := by
  have hx : |sharedSecondN02700PlusPointPosition2576| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [sharedSecondN02700PlusPointPosition2576, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) sharedSecondN02700PlusPointPosition2576 = embedPair2542
          sharedSecondN02700PlusPointP007Factor2576 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      sharedSecondN02700PlusPointPosition2576, storedWidth, nodeModulation2541, embedPair2542,
      sharedSecondN02700PlusPointP007Factor2576, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ sharedSecondN02700PlusPointP007BaseError2576
    (embedPair_magnitude2542 sharedSecondN02700PlusPointP007Factor2576)

def sharedSecondN02700PlusPointP008Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP008Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP008Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP008Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP008Exterior2555 n

theorem sharedSecondN02700PlusPointP008BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP008Center2576‖ ≤
          sharedSecondN02700PlusPointP008Error2576 := by
  exact kernelN02700PlusP008BaseError2555

theorem sharedSecondN02700PlusPointP008DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP008Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP008Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP008Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP008Error2576 := by
  rw [sharedSecondN02700PlusPointP008Exterior2576]
  norm_num [sharedSecondN02700PlusPointP008Factor2576, sharedSecondN02700PlusPointP008Center2576,
      sharedSecondN02700PlusPointP008Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP009Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP009Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP009Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP009Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP009Exterior2555 n

theorem sharedSecondN02700PlusPointP009BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP009Center2576‖ ≤
          sharedSecondN02700PlusPointP009Error2576 := by
  exact kernelN02700PlusP009BaseError2555

theorem sharedSecondN02700PlusPointP009DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP009Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP009Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP009Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP009Error2576 := by
  rw [sharedSecondN02700PlusPointP009Exterior2576]
  norm_num [sharedSecondN02700PlusPointP009Factor2576, sharedSecondN02700PlusPointP009Center2576,
      sharedSecondN02700PlusPointP009Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP010Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP010Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP010Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP010Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP010Exterior2555 n

theorem sharedSecondN02700PlusPointP010BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP010Center2576‖ ≤
          sharedSecondN02700PlusPointP010Error2576 := by
  exact kernelN02700PlusP010BaseError2555

theorem sharedSecondN02700PlusPointP010DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP010Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP010Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP010Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP010Error2576 := by
  rw [sharedSecondN02700PlusPointP010Exterior2576]
  norm_num [sharedSecondN02700PlusPointP010Factor2576, sharedSecondN02700PlusPointP010Center2576,
      sharedSecondN02700PlusPointP010Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP011Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP011Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP011Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP011Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP011Exterior2555 n

theorem sharedSecondN02700PlusPointP011BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP011Center2576‖ ≤
          sharedSecondN02700PlusPointP011Error2576 := by
  exact kernelN02700PlusP011BaseError2555

theorem sharedSecondN02700PlusPointP011DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP011Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP011Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP011Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP011Error2576 := by
  rw [sharedSecondN02700PlusPointP011Exterior2576]
  norm_num [sharedSecondN02700PlusPointP011Factor2576, sharedSecondN02700PlusPointP011Center2576,
      sharedSecondN02700PlusPointP011Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP012Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP012Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP012Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP012Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP012Exterior2555 n

theorem sharedSecondN02700PlusPointP012BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP012Center2576‖ ≤
          sharedSecondN02700PlusPointP012Error2576 := by
  exact kernelN02700PlusP012BaseError2555

theorem sharedSecondN02700PlusPointP012DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP012Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP012Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP012Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP012Error2576 := by
  rw [sharedSecondN02700PlusPointP012Exterior2576]
  norm_num [sharedSecondN02700PlusPointP012Factor2576, sharedSecondN02700PlusPointP012Center2576,
      sharedSecondN02700PlusPointP012Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP013Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP013Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP013Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP013Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP013Exterior2555 n

theorem sharedSecondN02700PlusPointP013BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP013Center2576‖ ≤
          sharedSecondN02700PlusPointP013Error2576 := by
  exact kernelN02700PlusP013BaseError2555

theorem sharedSecondN02700PlusPointP013DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP013Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP013Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP013Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP013Error2576 := by
  rw [sharedSecondN02700PlusPointP013Exterior2576]
  norm_num [sharedSecondN02700PlusPointP013Factor2576, sharedSecondN02700PlusPointP013Center2576,
      sharedSecondN02700PlusPointP013Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP014Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP014Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP014Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP014Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP014Exterior2555 n

theorem sharedSecondN02700PlusPointP014BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP014Center2576‖ ≤
          sharedSecondN02700PlusPointP014Error2576 := by
  exact kernelN02700PlusP014BaseError2555

theorem sharedSecondN02700PlusPointP014DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP014Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP014Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP014Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP014Error2576 := by
  rw [sharedSecondN02700PlusPointP014Exterior2576]
  norm_num [sharedSecondN02700PlusPointP014Factor2576, sharedSecondN02700PlusPointP014Center2576,
      sharedSecondN02700PlusPointP014Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP015Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP015Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP015Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP015Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP015Exterior2555 n

theorem sharedSecondN02700PlusPointP015BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP015Center2576‖ ≤
          sharedSecondN02700PlusPointP015Error2576 := by
  exact kernelN02700PlusP015BaseError2555

theorem sharedSecondN02700PlusPointP015DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP015Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP015Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP015Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP015Error2576 := by
  rw [sharedSecondN02700PlusPointP015Exterior2576]
  norm_num [sharedSecondN02700PlusPointP015Factor2576, sharedSecondN02700PlusPointP015Center2576,
      sharedSecondN02700PlusPointP015Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP016Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP016Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP016Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP016Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP016Exterior2555 n

theorem sharedSecondN02700PlusPointP016BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP016Center2576‖ ≤
          sharedSecondN02700PlusPointP016Error2576 := by
  exact kernelN02700PlusP016BaseError2555

theorem sharedSecondN02700PlusPointP016DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP016Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP016Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP016Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP016Error2576 := by
  rw [sharedSecondN02700PlusPointP016Exterior2576]
  norm_num [sharedSecondN02700PlusPointP016Factor2576, sharedSecondN02700PlusPointP016Center2576,
      sharedSecondN02700PlusPointP016Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP017Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP017Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP017Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP017Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP017Exterior2555 n

theorem sharedSecondN02700PlusPointP017BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP017Center2576‖ ≤
          sharedSecondN02700PlusPointP017Error2576 := by
  exact kernelN02700PlusP017BaseError2555

theorem sharedSecondN02700PlusPointP017DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP017Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP017Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP017Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP017Error2576 := by
  rw [sharedSecondN02700PlusPointP017Exterior2576]
  norm_num [sharedSecondN02700PlusPointP017Factor2576, sharedSecondN02700PlusPointP017Center2576,
      sharedSecondN02700PlusPointP017Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP018Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP018Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP018Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP018Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP018Exterior2555 n

theorem sharedSecondN02700PlusPointP018BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP018Center2576‖ ≤
          sharedSecondN02700PlusPointP018Error2576 := by
  exact kernelN02700PlusP018BaseError2555

theorem sharedSecondN02700PlusPointP018DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP018Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP018Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP018Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP018Error2576 := by
  rw [sharedSecondN02700PlusPointP018Exterior2576]
  norm_num [sharedSecondN02700PlusPointP018Factor2576, sharedSecondN02700PlusPointP018Center2576,
      sharedSecondN02700PlusPointP018Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP019Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP019Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP019Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP019Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP019Exterior2555 n

theorem sharedSecondN02700PlusPointP019BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP019Center2576‖ ≤
          sharedSecondN02700PlusPointP019Error2576 := by
  exact kernelN02700PlusP019BaseError2555

theorem sharedSecondN02700PlusPointP019DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP019Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP019Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP019Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP019Error2576 := by
  rw [sharedSecondN02700PlusPointP019Exterior2576]
  norm_num [sharedSecondN02700PlusPointP019Factor2576, sharedSecondN02700PlusPointP019Center2576,
      sharedSecondN02700PlusPointP019Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP020Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP020Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP020Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP020Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP020Exterior2555 n

theorem sharedSecondN02700PlusPointP020BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP020Center2576‖ ≤
          sharedSecondN02700PlusPointP020Error2576 := by
  exact kernelN02700PlusP020BaseError2555

theorem sharedSecondN02700PlusPointP020DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP020Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP020Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP020Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP020Error2576 := by
  rw [sharedSecondN02700PlusPointP020Exterior2576]
  norm_num [sharedSecondN02700PlusPointP020Factor2576, sharedSecondN02700PlusPointP020Center2576,
      sharedSecondN02700PlusPointP020Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP021Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP021Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP021Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP021Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP021Exterior2555 n

theorem sharedSecondN02700PlusPointP021BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP021Center2576‖ ≤
          sharedSecondN02700PlusPointP021Error2576 := by
  exact kernelN02700PlusP021BaseError2555

theorem sharedSecondN02700PlusPointP021DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP021Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP021Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP021Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP021Error2576 := by
  rw [sharedSecondN02700PlusPointP021Exterior2576]
  norm_num [sharedSecondN02700PlusPointP021Factor2576, sharedSecondN02700PlusPointP021Center2576,
      sharedSecondN02700PlusPointP021Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP022Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP022Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP022Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP022Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP022Exterior2555 n

theorem sharedSecondN02700PlusPointP022BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP022Center2576‖ ≤
          sharedSecondN02700PlusPointP022Error2576 := by
  exact kernelN02700PlusP022BaseError2555

theorem sharedSecondN02700PlusPointP022DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP022Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP022Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP022Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP022Error2576 := by
  rw [sharedSecondN02700PlusPointP022Exterior2576]
  norm_num [sharedSecondN02700PlusPointP022Factor2576, sharedSecondN02700PlusPointP022Center2576,
      sharedSecondN02700PlusPointP022Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP023Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP023Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP023Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP023Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP023Exterior2555 n

theorem sharedSecondN02700PlusPointP023BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP023Center2576‖ ≤
          sharedSecondN02700PlusPointP023Error2576 := by
  exact kernelN02700PlusP023BaseError2555

theorem sharedSecondN02700PlusPointP023DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP023Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP023Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP023Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP023Error2576 := by
  rw [sharedSecondN02700PlusPointP023Exterior2576]
  norm_num [sharedSecondN02700PlusPointP023Factor2576, sharedSecondN02700PlusPointP023Center2576,
      sharedSecondN02700PlusPointP023Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP024Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP024Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP024Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP024Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP024Exterior2555 n

theorem sharedSecondN02700PlusPointP024BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP024Center2576‖ ≤
          sharedSecondN02700PlusPointP024Error2576 := by
  exact kernelN02700PlusP024BaseError2555

theorem sharedSecondN02700PlusPointP024DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP024Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP024Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP024Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP024Error2576 := by
  rw [sharedSecondN02700PlusPointP024Exterior2576]
  norm_num [sharedSecondN02700PlusPointP024Factor2576, sharedSecondN02700PlusPointP024Center2576,
      sharedSecondN02700PlusPointP024Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP025Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP025Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP025Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP025Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP025Exterior2555 n

theorem sharedSecondN02700PlusPointP025BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP025Center2576‖ ≤
          sharedSecondN02700PlusPointP025Error2576 := by
  exact kernelN02700PlusP025BaseError2555

theorem sharedSecondN02700PlusPointP025DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP025Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP025Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP025Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP025Error2576 := by
  rw [sharedSecondN02700PlusPointP025Exterior2576]
  norm_num [sharedSecondN02700PlusPointP025Factor2576, sharedSecondN02700PlusPointP025Center2576,
      sharedSecondN02700PlusPointP025Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP026Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP026Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP026Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP026Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP026Exterior2555 n

theorem sharedSecondN02700PlusPointP026BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP026Center2576‖ ≤
          sharedSecondN02700PlusPointP026Error2576 := by
  exact kernelN02700PlusP026BaseError2555

theorem sharedSecondN02700PlusPointP026DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP026Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP026Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP026Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP026Error2576 := by
  rw [sharedSecondN02700PlusPointP026Exterior2576]
  norm_num [sharedSecondN02700PlusPointP026Factor2576, sharedSecondN02700PlusPointP026Center2576,
      sharedSecondN02700PlusPointP026Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP027Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP027Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP027Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP027Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP027Exterior2555 n

theorem sharedSecondN02700PlusPointP027BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP027Center2576‖ ≤
          sharedSecondN02700PlusPointP027Error2576 := by
  exact kernelN02700PlusP027BaseError2555

theorem sharedSecondN02700PlusPointP027DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP027Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP027Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP027Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP027Error2576 := by
  rw [sharedSecondN02700PlusPointP027Exterior2576]
  norm_num [sharedSecondN02700PlusPointP027Factor2576, sharedSecondN02700PlusPointP027Center2576,
      sharedSecondN02700PlusPointP027Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP028Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP028Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP028Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP028Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP028Exterior2555 n

theorem sharedSecondN02700PlusPointP028BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP028Center2576‖ ≤
          sharedSecondN02700PlusPointP028Error2576 := by
  exact kernelN02700PlusP028BaseError2555

theorem sharedSecondN02700PlusPointP028DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP028Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP028Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP028Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP028Error2576 := by
  rw [sharedSecondN02700PlusPointP028Exterior2576]
  norm_num [sharedSecondN02700PlusPointP028Factor2576, sharedSecondN02700PlusPointP028Center2576,
      sharedSecondN02700PlusPointP028Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

def sharedSecondN02700PlusPointP029Center2576 : RatPair2542 := (0, 0)

def sharedSecondN02700PlusPointP029Factor2576 : RatPair2542 := (0, 0)

noncomputable def sharedSecondN02700PlusPointP029Error2576 : ℝ := 0

theorem sharedSecondN02700PlusPointP029Exterior2576 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02700PlusPointPosition2576 = 0 := by
  exact kernelN02700PlusP029Exterior2555 n

theorem sharedSecondN02700PlusPointP029BaseError2576 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP029Center2576‖ ≤
          sharedSecondN02700PlusPointP029Error2576 := by
  exact kernelN02700PlusP029BaseError2555

theorem sharedSecondN02700PlusPointP029DerivativeError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP029Factor2576 * embedPair2542
          sharedSecondN02700PlusPointP029Center2576‖ ≤
        (pairMagnitude2542 sharedSecondN02700PlusPointP029Factor2576 : ℝ) *
            sharedSecondN02700PlusPointP029Error2576 := by
  rw [sharedSecondN02700PlusPointP029Exterior2576]
  norm_num [sharedSecondN02700PlusPointP029Factor2576, sharedSecondN02700PlusPointP029Center2576,
      sharedSecondN02700PlusPointP029Error2576,
      sharedSecondN02700PlusPointZero2576, pairMagnitude2542]

theorem sharedSecondN02700PlusPointGrid2576 :
    -stripRadius2303 + (2700 : ℝ) * (2 * stripRadius2303 / 10240) =
      sharedSecondN02700PlusPointPosition2576 := by
  norm_num [stripRadius2303, sharedSecondN02700PlusPointPosition2576]

end ConnesWeilRH.Dev
