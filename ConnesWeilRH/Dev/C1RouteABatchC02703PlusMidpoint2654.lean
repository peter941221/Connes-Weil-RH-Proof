import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchC02703PlusMidpointPosition2654 : ℝ := (((-316735492833) : ℝ) /
        102400000000)

theorem batchC02703PlusMidpointZero2654 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchC02703PlusMidpointP000Center2654 : RatPair2542 := (0, 0)

def batchC02703PlusMidpointP000Factor2654 : RatPair2542 := (0, 0)

noncomputable def batchC02703PlusMidpointP000Error2654 : ℝ := 0

theorem batchC02703PlusMidpointP000Exterior2654 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02703PlusMidpointPosition2654 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |batchC02703PlusMidpointPosition2654| := by
    norm_num [storedWidth, batchC02703PlusMidpointPosition2654]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem batchC02703PlusMidpointP000BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP000Center2654‖ ≤ batchC02703PlusMidpointP000Error2654
          := by
  rw [batchC02703PlusMidpointP000Exterior2654]
  norm_num [batchC02703PlusMidpointP000Center2654, batchC02703PlusMidpointP000Error2654,
      batchC02703PlusMidpointZero2654]

theorem batchC02703PlusMidpointP000DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP000Factor2654 * embedPair2542
          batchC02703PlusMidpointP000Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP000Factor2654 : ℝ) *
            batchC02703PlusMidpointP000Error2654 := by
  rw [batchC02703PlusMidpointP000Exterior2654]
  norm_num [batchC02703PlusMidpointP000Factor2654, batchC02703PlusMidpointP000Center2654,
      batchC02703PlusMidpointP000Error2654,
      batchC02703PlusMidpointZero2654, pairMagnitude2542]

def batchC02703PlusMidpointP001Input2654 : RatPair2542 :=
    ((((-(9331677822110049723003284555183727295628 *
    10^40
        + 9490751286013211077439470202441761765417)) : ℚ) /
        ((2 * 10^40
        + 6105795989954410616908676258371734840964) * 10^40
        + 7085517164747000628154230269542400000000)),
    ((1749739040583718993008386157 : ℚ) /
        7378697629483820646400000000))

def batchC02703PlusMidpointP001Center2654 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP001Factor2654 : RatPair2542 := ((((((((((236955341597875846155 * 10^40
        + 7631740333783273173694832797719858766064) * 10^40
        + 5934953580735896965646342271150771410198) * 10^40
        + 4510790874414147447215353318902838128121) * 10^40
        + 5260717211047058090441764745609765929410) * 10^40
        + 6163231390614376317678368087039624492885) * 10^40
        + 5204868893534528789530886806601603421853) * 10^40
        + 2088042991584642883571880656162808048495) : ℚ) /
        (((((((684873256575724 * 10^40
        + 2370140998274624055002488004123915834298) * 10^40
        + 8089970320597692648080808394183498962723) * 10^40
        + 7079859102305490765553462129060756538270) * 10^40
        + 9395243675980792162292799876635620380601) * 10^40
        + 4969621022290337072789875449736420652707) * 10^40
        + 8152520742871246570624020783295022628009) * 10^40
        + 9291125434145921407965473005619963232256)),
    (((-(((40606508859853433189700512511297 * 10^40
        + 5660627089522272562569733499409254168131) * 10^40
        + 9240118148483608909002855258423306462055) * 10^40
        + 311922943997435954237591719800303216029)) : ℚ) /
        (((872336107864473325864215004 * 10^40
        + 3083119694800333575110962220020458067639) * 10^40
        + 4911086349577617206369127334737239996814) * 10^40
        + 6739671780504839054352608273370949091328)))

noncomputable def batchC02703PlusMidpointP001Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP001BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP001Center2654‖ ≤ batchC02703PlusMidpointP001Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP001Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP001Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP001Input2654 9 =
      (batchC02703PlusMidpointP001Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP001Input2654 9).2 : ℝ) =
      batchC02703PlusMidpointP001Error2654 := by
    rw [hs]
    norm_num [batchC02703PlusMidpointP001Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP001Input2654 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          batchC02703PlusMidpointP001Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP001Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP001DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP001Factor2654 * embedPair2542
          batchC02703PlusMidpointP001Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP001Factor2654 : ℝ) *
            batchC02703PlusMidpointP001Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP001Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP001Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP001BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP001Factor2654)

def batchC02703PlusMidpointP002Input2654 : RatPair2542 := ((((-((223 * 10^40
        + 632682565726268228209328454776902230798) * 10^40
        + 5401053942436431768743065191805344610673)) : ℚ) /
        ((907 * 10^40
        + 6566688093805892399028352450919822243973) * 10^40
        + 5562169296946165227104579407052800000000)),
    (((-1749739040583718993008386157) : ℚ) /
        3689348814741910323200000000))

def batchC02703PlusMidpointP002Center2654 : RatPair2542 := ((((-309065072177326647275) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-310951153252216976051) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC02703PlusMidpointP002Factor2654 : RatPair2542 := ((((((((((73382664557951784043563391840
    * 10^40
        + 7964296003398132221607867695250491499866) * 10^40
        + 9667885431183739917226113081630056509596) * 10^40
        + 9960715831732931695803817306077827811479) * 10^40
        + 7028630948429339525329030229693874499040) * 10^40
        + 1816179234122740534452109560087130439380) * 10^40
        + 6889443191094346958404742340936404397044) * 10^40
        + 7551900699932336289420440649965696120685) : ℚ) /
        (((((((480385729523523435726859879 * 10^40
        + 2775216011231556979761304011622474958341) * 10^40
        + 15830441943907989341034779726937110421) * 10^40
        + 5658583955982579854750334187300077732517) * 10^40
        + 9727265293890335306969300400259610548921) * 10^40
        + 2584695690484231275698265184139082278852) * 10^40
        + 4986820186651225289806278557987509658566) * 10^40
        + 4491828599305430759480867966189230358528)),
    (((((1390397426416721263500070660414633207 * 10^40
        + 757068464166118970415509168268512664266) * 10^40
        + 3013050063889989585040956466298178024667) * 10^40
        + 4181539957832776476327341971500817655469) : ℚ) /
        (((421806401758280500327337297102314 * 10^40
        + 8140150076674282230220238386611892008295) * 10^40
        + 687681922515014871635317358694198419023) * 10^40
        + 9246120977791785609131556620000357777408)))

noncomputable def batchC02703PlusMidpointP002Error2654 : ℝ := ((1312739029766369773 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC02703PlusMidpointP002BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP002Center2654‖ ≤ batchC02703PlusMidpointP002Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP002Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP002Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP002Input2654 8 =
      (batchC02703PlusMidpointP002Center2654, ((1312739029766369773 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP002Input2654 8).2 : ℝ) =
      batchC02703PlusMidpointP002Error2654 := by
    rw [hs]
    norm_num [batchC02703PlusMidpointP002Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP002Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02703PlusMidpointP002Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP002Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP002DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP002Factor2654 * embedPair2542
          batchC02703PlusMidpointP002Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP002Factor2654 : ℝ) *
            batchC02703PlusMidpointP002Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP002Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP002Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP002BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP002Factor2654)

def batchC02703PlusMidpointP003Input2654 : RatPair2542 := ((((-((7224106 * 10^40
        + 8554056984434567764537471683047795481612) * 10^40
        + 9300076989499982013849036870504997305953)) : ℚ) /
        ((39909323 * 10^40
        + 2173098595058318439849977628536462222717) * 10^40
        + 7075397844561261240558584646860800000000)),
    (((-1749739040583718993008386157) : ℚ) /
        3689348814741910323200000000))

def batchC02703PlusMidpointP003Center2654 : RatPair2542 := ((((-609806471203643622163728095) : ℚ)
    /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    (((-2454111351316243095425241341) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchC02703PlusMidpointP003Factor2654 : RatPair2542 := ((((-((((((((8884655 * 10^40
        + 7366767238710150735763298660036668548413) * 10^40
        + 2771334633707042250956562381182121137204) * 10^40
        + 7113321181563000382846340347070503540342) * 10^40
        + 8845253919303318863490387378695087592674) * 10^40
        + 7546925586325481580516758322895284251005) * 10^40
        + 5791193034301573262328060703976100652936) * 10^40
        + 9328480475442697834137971041117108151889) * 10^40
        + 9363522718078089548020680386389719039145)) : ℚ) /
        ((((((((6650 * 10^40
        + 2408491116392305360750374304171148880015) * 10^40
        + 8888519693162406535793642164592918910006) * 10^40
        + 4530433710676354504923695640497324738458) * 10^40
        + 474708301784417656819782432434936751540) * 10^40
        + 6207645351261312099665966688738336505321) * 10^40
        + 2489225876476505527844576104121433734986) * 10^40
        + 7256772275000525081059431851505002049817) * 10^40
        + 156564114883576411595615598893307265024)),
    ((((((94630 * 10^40
        + 1900474400078296234111116917789320872357) * 10^40
        + 8023782852165521404066039855974407547948) * 10^40
        + 9334417311381617779921581618099073557863) * 10^40
        + 3275202848907520579950774979197071873549) : ℚ) /
        ((((81 * 10^40
        + 5490088787818391259802587653191878682990) * 10^40
        + 5592798717137792896144614007283126629840) * 10^40
        + 8169378537463451588299065414406849324310) * 10^40
        + 7748156047340878143410821357736682323968)))

noncomputable def batchC02703PlusMidpointP003Error2654 : ℝ := ((38843828102563552105294473 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP003BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP003Center2654‖ ≤ batchC02703PlusMidpointP003Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP003Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP003Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP003Input2654 8 =
      (batchC02703PlusMidpointP003Center2654, ((38843828102563552105294473 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP003Input2654 8).2 : ℝ) =
      batchC02703PlusMidpointP003Error2654 := by
    rw [hs]
    norm_num [batchC02703PlusMidpointP003Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP003Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02703PlusMidpointP003Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP003Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP003DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP003Factor2654 * embedPair2542
          batchC02703PlusMidpointP003Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP003Factor2654 : ℝ) *
            batchC02703PlusMidpointP003Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP003Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP003Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP003BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP003Factor2654)

def batchC02703PlusMidpointP004Input2654 : RatPair2542 := ((((-((57 * 10^40
        + 6958596485091301486426632849314948524033) * 10^40
        + 4459204821600089090587166529015698012297)) : ℚ) /
        ((367 * 10^40
        + 9235794181140936530116772061806973257075) * 10^40
        + 3233813500783245025233842156339200000000)),
    ((1749739040583718993008386157 : ℚ) /
        3689348814741910323200000000))

def batchC02703PlusMidpointP004Center2654 : RatPair2542 := ((((-298906548708990247551681640363) :
    ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((2405845096138794465498501925661 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC02703PlusMidpointP004Factor2654 : RatPair2542 :=
    ((((-(((((((6429372033148292297254431540 * 10^40
        + 3816937262111891773589403052044114607711) * 10^40
        + 2091494348105416351852617978332019943214) * 10^40
        + 9891039048212244361618237987919609486957) * 10^40
        + 4721168163834159342094219247026036705199) * 10^40
        + 1372153203432145922345252055773856910864) * 10^40
        + 424066439344714103863309960590412616306) * 10^40
        + 2203218805769920098735043273446352972305)) : ℚ) /
        (((((((4323275564328024290765888 * 10^40
        + 577796549450561173324521435512667847094) * 10^40
        + 143690981248927661524289161612659297436) * 10^40
        + 3697326703760821531686382783935428510357) * 10^40
        + 9511936665947723534268286380581151786561) * 10^40
        + 2329944432892520785389832690094461582735) * 10^40
        + 5346428983474055333529662657433530506872) * 10^40
        + 872872799447661823459696309910389129216)),
    (((-(((41639174510390181321678307703343261 * 10^40
        + 7535497832085044233911758757459152282196) * 10^40
        + 9492654641075990645075938195593353579791) * 10^40
        + 823129027942621869362721035021422131549)) : ℚ) /
        (((69308293269420702059076544575621 * 10^40
        + 5633177325419984539322170168813258063842) * 10^40
        + 7525751726261002576446366634684657373192) * 10^40
        + 2454077087469085869006917982962967379968)))

noncomputable def batchC02703PlusMidpointP004Error2654 : ℝ := ((9292365319340215854689318283 : ℝ)
    /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC02703PlusMidpointP004BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP004Center2654‖ ≤ batchC02703PlusMidpointP004Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP004Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP004Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP004Input2654 8 =
      (batchC02703PlusMidpointP004Center2654, ((9292365319340215854689318283 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP004Input2654 8).2 : ℝ) =
      batchC02703PlusMidpointP004Error2654 := by
    rw [hs]
    norm_num [batchC02703PlusMidpointP004Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP004Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02703PlusMidpointP004Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP004Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP004DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP004Factor2654 * embedPair2542
          batchC02703PlusMidpointP004Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP004Factor2654 : ℝ) *
            batchC02703PlusMidpointP004Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP004Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP004Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP004BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP004Factor2654)

def batchC02703PlusMidpointP005Center2654 : RatPair2542 := (0, 0)

def batchC02703PlusMidpointP005Factor2654 : RatPair2542 := (0, 0)

noncomputable def batchC02703PlusMidpointP005Error2654 : ℝ := 0

theorem batchC02703PlusMidpointP005Exterior2654 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02703PlusMidpointPosition2654 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |batchC02703PlusMidpointPosition2654| := by
    norm_num [storedWidth, batchC02703PlusMidpointPosition2654]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem batchC02703PlusMidpointP005BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP005Center2654‖ ≤ batchC02703PlusMidpointP005Error2654
          := by
  rw [batchC02703PlusMidpointP005Exterior2654]
  norm_num [batchC02703PlusMidpointP005Center2654, batchC02703PlusMidpointP005Error2654,
      batchC02703PlusMidpointZero2654]

theorem batchC02703PlusMidpointP005DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP005Factor2654 * embedPair2542
          batchC02703PlusMidpointP005Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP005Factor2654 : ℝ) *
            batchC02703PlusMidpointP005Error2654 := by
  rw [batchC02703PlusMidpointP005Exterior2654]
  norm_num [batchC02703PlusMidpointP005Factor2654, batchC02703PlusMidpointP005Center2654,
      batchC02703PlusMidpointP005Error2654,
      batchC02703PlusMidpointZero2654, pairMagnitude2542]

def batchC02703PlusMidpointP006Input2654 : RatPair2542 :=
    ((((-1052156209486073542619134012060826463) : ℚ) /
        1768181925932868714734839398400000000),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP006Center2654 : RatPair2542 := (((609727932935713 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP006Factor2654 : RatPair2542 := (((((4189922001790857 * 10^40
        + 3595916053775204466676191693644288621239) * 10^40
        + 436408098525674774196473074014740023041) : ℚ) /
        ((827957589354 * 10^40
        + 2620074908263472570046885954478345606089) * 10^40
        + 602636945803179096785892296058960092164)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP006Error2654 : ℝ := ((2510196827635 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP006BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP006Center2654‖ ≤ batchC02703PlusMidpointP006Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP006Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP006Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP006Input2654 7 =
      (batchC02703PlusMidpointP006Center2654, ((2510196827635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP006Input2654 7).2 : ℝ) =
      batchC02703PlusMidpointP006Error2654 := by
    rw [hs]
    norm_num [batchC02703PlusMidpointP006Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP006Input2654 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          batchC02703PlusMidpointP006Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP006Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP006DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP006Factor2654 * embedPair2542
          batchC02703PlusMidpointP006Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP006Factor2654 : ℝ) *
            batchC02703PlusMidpointP006Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP006Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP006Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP006BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP006Factor2654)

def batchC02703PlusMidpointP007Input2654 : RatPair2542 := ((((-((7224106 * 10^40
        + 8554056984434567764537471683047795481612) * 10^40
        + 9300076989499982013849036870504997305953)) : ℚ) /
        ((9977330 * 10^40
        + 8043274648764579609962494407134115555679) * 10^40
        + 4268849461140315310139646161715200000000)),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP007Center2654 : RatPair2542 := (((1370229748431499141211097531 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP007Factor2654 : RatPair2542 := ((((((((((2750000398290884175 * 10^40
        + 3339037535848117337881495791077680880107) * 10^40
        + 5907000647774763127690002283836236633322) * 10^40
        + 6579121843256667156493003695588937199803) * 10^40
        + 1853922121905826202814460387264127652023) * 10^40
        + 1612578902316904290532658415560049106797) * 10^40
        + 8985423169566117426955205053064864763896) * 10^40
        + 1029765354830927378705834711869370396161) : ℚ) /
        (((((((13430054441389972 * 10^40
        + 2391531057807732993606177861224085965674) * 10^40
        + 4541038191545642410236064673779875047485) * 10^40
        + 2974384389092509867159402550158979206813) * 10^40
        + 9055339083166401027717051401113358631398) * 10^40
        + 6387680231754923059765005555281878603047) * 10^40
        + 8698142665837978369254917285640268386974) * 10^40
        + 4859669419323709514823338847477481584644)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP007Error2654 : ℝ := ((1591164170785539191340877 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP007BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP007Center2654‖ ≤ batchC02703PlusMidpointP007Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP007Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP007Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP007Input2654 6 =
      (batchC02703PlusMidpointP007Center2654, ((1591164170785539191340877 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP007Input2654 6).2 : ℝ) =
      batchC02703PlusMidpointP007Error2654 := by
    rw [hs]
    norm_num [batchC02703PlusMidpointP007Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP007Input2654 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          batchC02703PlusMidpointP007Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP007Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP007DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP007Factor2654 * embedPair2542
          batchC02703PlusMidpointP007Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP007Factor2654 : ℝ) *
            batchC02703PlusMidpointP007Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP007Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP007Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP007BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP007Factor2654)

def batchC02703PlusMidpointP008Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1260154782678093206550844401 : ℚ) /
        472236648286964521369600000000))

def batchC02703PlusMidpointP008Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP008Factor2654 : RatPair2542 := (((((((((((595045 * 10^40
        + 4653438214369769569016286249385747722338) * 10^40
        + 8901258658546300520988436972471753216484) * 10^40
        + 1409267244872209818046007168781698989260) * 10^40
        + 2216721231544327501813162749594092712743) * 10^40
        + 3545000774593854448300030013328456111589) * 10^40
        + 8315201518690171790329399799179561332469) * 10^40
        + 3555958834214940692157705698624659647967) * 10^40
        + 391899707251124465671455522320825945375) : ℚ) /
        (((((((1110439080628680299099986960941600 * 10^40
        + 2657103405942841666364752370186768464667) * 10^40
        + 9270380565708012113814295317813744068646) * 10^40
        + 698111232335582801608470202915489884157) * 10^40
        + 8865146144447876850326522351656108407076) * 10^40
        + 9011902430559518560961483140217351149084) * 10^40
        + 8268336972108683727698227758310661785228) * 10^40
        + 5006197847838498008632702395573229060096)),
    (((-((((21808 * 10^40
        + 9278721215459337026841990896354235556210) * 10^40
        + 1070164549760225527572029960593303942864) * 10^40
        + 4784582816656273309354285901719221564488) * 10^40
        + 8783530156500564542032079345156764092657)) : ℚ) /
        (((3332325135140147603871227328263866455 * 10^40
        + 5005702969657625053787045271971239654632) * 10^40
        + 2635559150742289720293477249947721890321) * 10^40
        + 8490702832146132629431562715473364647936)))

noncomputable def batchC02703PlusMidpointP008Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP008BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP008Center2654‖ ≤ batchC02703PlusMidpointP008Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP008Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP008Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP008Input2654 14 =
      (batchC02703PlusMidpointP008Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP008Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP008Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP008Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP008Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP008Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP008Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP008DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP008Factor2654 * embedPair2542
          batchC02703PlusMidpointP008Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP008Factor2654 : ℝ) *
            batchC02703PlusMidpointP008Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP008Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP008Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP008BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP008Factor2654)

def batchC02703PlusMidpointP009Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1874180327301030250642993263 : ℚ) /
        472236648286964521369600000000))

def batchC02703PlusMidpointP009Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP009Factor2654 : RatPair2542 := (((((((((((595045 * 10^40
        + 4653169337430402774639410594283411905714) * 10^40
        + 9836335832918234454543485209222284503681) * 10^40
        + 2597492955340162484749103613419505397676) * 10^40
        + 2176028668036713902309802194667727018591) * 10^40
        + 257320230699555856798226538205989782683) * 10^40
        + 5685055253065728025316429685493176326184) * 10^40
        + 3402898892077528865010659916337719276933) * 10^40
        + 8086930446239423725217309693687241074143) : ℚ) /
        (((((((1110439080628680299099986960941600 * 10^40
        + 2657103405942841666364752370186768464667) * 10^40
        + 9270380565708012113814295317813744068646) * 10^40
        + 698111232335582801608470202915489884157) * 10^40
        + 8865146144447876850326522351656108407076) * 10^40
        + 9011902430559518560961483140217351149084) * 10^40
        + 8268336972108683727698227758310661785228) * 10^40
        + 5006197847838498008632702395573229060096)),
    (((-((((1046 * 10^40
        + 3093474144191150733555439313286541117085) * 10^40
        + 823359163851105982096851868148815312786) * 10^40
        + 7213647992897949419227535117093694983977) * 10^40
        + 9555870283479257466115963454711038032561)) : ℚ) /
        (((107494359198069277544233139621415046 * 10^40
        + 9516312999021213711412485331353910956601) * 10^40
        + 407598682282009345815918620966055544849) * 10^40
        + 919054930069230084820372990821721440256)))

noncomputable def batchC02703PlusMidpointP009Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP009BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP009Center2654‖ ≤ batchC02703PlusMidpointP009Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP009Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP009Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP009Input2654 14 =
      (batchC02703PlusMidpointP009Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP009Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP009Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP009Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP009Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP009Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP009Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP009DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP009Factor2654 * embedPair2542
          batchC02703PlusMidpointP009Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP009Factor2654 : ℝ) *
            batchC02703PlusMidpointP009Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP009Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP009Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP009BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP009Factor2654)

def batchC02703PlusMidpointP010Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1114897936905804466764951993 : ℚ) /
        236118324143482260684800000000))

def batchC02703PlusMidpointP010Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP010Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 3663241360527096745038425676545233752435) * 10^40
        + 3183528149269871795867171008386656262831) * 10^40
        + 1086595570717382136917292854148268678522) * 10^40
        + 5767425891812319063630000960088558373989) * 10^40
        + 4554719330398347432178954304377244836582) * 10^40
        + 5170468789596526320460830668117454584537) * 10^40
        + 2405048156135482628014548860883679461858) * 10^40
        + 2465322892797405394214248222747074674255) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((19295 * 10^40
        + 334553997484082545321309649701368612248) * 10^40
        + 8842491072828262586382488820841322251719) * 10^40
        + 3636432633456224412177117983847357819400) * 10^40
        + 958410811917438326213150495870105571001)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703PlusMidpointP010Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP010BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP010Center2654‖ ≤ batchC02703PlusMidpointP010Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP010Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP010Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP010Input2654 14 =
      (batchC02703PlusMidpointP010Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP010Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP010Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP010Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP010Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP010Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP010Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP010DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP010Factor2654 * embedPair2542
          batchC02703PlusMidpointP010Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP010Factor2654 : ℝ) *
            batchC02703PlusMidpointP010Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP010Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP010Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP010BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP010Factor2654)

def batchC02703PlusMidpointP011Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1233447703055322478455772233 : ℚ) /
        236118324143482260684800000000))

def batchC02703PlusMidpointP011Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP011Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 3663202466365912721870792765261088300372) * 10^40
        + 954992330418602049458553038682700959872) * 10^40
        + 7748512103784111799667296483750465101267) * 10^40
        + 5053864377575337475954107588583248237405) * 10^40
        + 3611427630111527182643568310410485261833) * 10^40
        + 3964795768643815606260849370445273931752) * 10^40
        + 5566297844302658701657886848251722782677) * 10^40
        + 9781197103641927301769988133708489480495) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((21346 * 10^40
        + 7205455499801666480715918045533927034123) * 10^40
        + 8954242182099448546855965359745533593875) * 10^40
        + 9453057026352028346967820747453579338112) * 10^40
        + 2323978427005249461950519536629568356681)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703PlusMidpointP011Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP011BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP011Center2654‖ ≤ batchC02703PlusMidpointP011Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP011Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP011Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP011Input2654 14 =
      (batchC02703PlusMidpointP011Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP011Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP011Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP011Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP011Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP011Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP011Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP011DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP011Factor2654 * embedPair2542
          batchC02703PlusMidpointP011Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP011Factor2654 : ℝ) *
            batchC02703PlusMidpointP011Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP011Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP011Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP011BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP011Factor2654)

def batchC02703PlusMidpointP012Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((27124724943668121973688997 : ℚ) /
        4722366482869645213696000000))

def batchC02703PlusMidpointP012Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP012Factor2654 : RatPair2542 := (((((((((((37190 * 10^40
        + 3415789510370422305826350755948435601968) * 10^40
        + 5740402530888961028321287476932977246939) * 10^40
        + 9533022120975155244935174319641974822523) * 10^40
        + 5954669109596113105871912261011324659417) * 10^40
        + 4167498202781290032804917458008576783057) * 10^40
        + 3609235465640816035065443913676768734684) * 10^40
        + 1151200061037222108642024346915024612200) * 10^40
        + 8798715551461713608836028814226512928439) : ℚ) /
        (((((((69402442539292518693749185058850 * 10^40
        + 166068962871427604147797023136673029041) * 10^40
        + 7454398785356750757113393457363359004290) * 10^40
        + 3793631952020973925100529387682218117759) * 10^40
        + 8679071634027992303145407646978506775442) * 10^40
        + 3063243901909969910060092696263584446817) * 10^40
        + 8016771060756792732981139234894416361576) * 10^40
        + 7812887365489906125539543899723326816256)),
    (((-((((11735 * 10^40
        + 8831228335832024573822827866788493947467) * 10^40
        + 6052663661605014921800221059999928284034) * 10^40
        + 7275780031078762049587945511319236542737) * 10^40
        + 6500937967544710488922605283312258685725)) : ℚ) /
        (((833081283785036900967806832065966613 * 10^40
        + 8751425742414406263446761317992809913658) * 10^40
        + 658889787685572430073369312486930472580) * 10^40
        + 4622675708036533157357890678868341161984)))

noncomputable def batchC02703PlusMidpointP012Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP012BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP012Center2654‖ ≤ batchC02703PlusMidpointP012Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP012Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP012Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP012Input2654 14 =
      (batchC02703PlusMidpointP012Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP012Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP012Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP012Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP012Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP012Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP012Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP012DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP012Factor2654 * embedPair2542
          batchC02703PlusMidpointP012Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP012Factor2654 : ℝ) *
            batchC02703PlusMidpointP012Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP012Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP012Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP012BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP012Factor2654)

def batchC02703PlusMidpointP013Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((293626334869738940090135403 : ℚ) /
        47223664828696452136960000000))

def batchC02703PlusMidpointP013Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP013Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 3663113888981795512329183101201347321658) * 10^40
        + 8183210252673331747310468449096303792102) * 10^40
        + 7275552709905223917305589032288887413394) * 10^40
        + 5774629865917980938011574191611196615503) * 10^40
        + 8940247972070235380487574153111071213587) * 10^40
        + 5707718370844865465191698156747280208527) * 10^40
        + 6497617647331657412148627943595927218020) * 10^40
        + 5776414608833329675067821812058804725231) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((25408 * 10^40
        + 2897059692561599477815080784196363703683) * 10^40
        + 8961453109843305674773523238283783188450) * 10^40
        + 9001654315202546023523583783693812688520) * 10^40
        + 378020526750282807371501165905037816855)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703PlusMidpointP013Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP013BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP013Center2654‖ ≤ batchC02703PlusMidpointP013Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP013Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP013Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP013Input2654 14 =
      (batchC02703PlusMidpointP013Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP013Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP013Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP013Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP013Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP013Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP013Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP013DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP013Factor2654 * embedPair2542
          batchC02703PlusMidpointP013Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP013Factor2654 : ℝ) *
            batchC02703PlusMidpointP013Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP013Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP013Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP013BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP013Factor2654)

def batchC02703PlusMidpointP014Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1675462440708706317018938163 : ℚ) /
        236118324143482260684800000000))

def batchC02703PlusMidpointP014Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP014Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 3663022832281272119057513712885774945549) * 10^40
        + 5005709179326933998388846255595653821934) * 10^40
        + 9674916840596873353522271042051587186212) * 10^40
        + 1178408191344519367692069770938228605648) * 10^40
        + 9327608754254274133676838998302651086339) * 10^40
        + 3061436638671192256534963540366379896067) * 10^40
        + 9522333302115672396054556913048536580154) * 10^40
        + 3865833030755612054097480750495303522775) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((28996 * 10^40
        + 4693418134324092839758050393551437594015) * 10^40
        + 9569728821580064717685991966013117206770) * 10^40
        + 1944422584639795499523908994899549973786) * 10^40
        + 7049789776035347139290154827483104688691)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703PlusMidpointP014Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP014BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP014Center2654‖ ≤ batchC02703PlusMidpointP014Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP014Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP014Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP014Input2654 14 =
      (batchC02703PlusMidpointP014Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP014Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP014Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP014Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP014Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP014Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP014Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP014DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP014Factor2654 * embedPair2542
          batchC02703PlusMidpointP014Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP014Factor2654 : ℝ) *
            batchC02703PlusMidpointP014Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP014Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP014Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP014BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP014Factor2654)

def batchC02703PlusMidpointP015Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1824015640458731668997834151 : ℚ) /
        236118324143482260684800000000))

def batchC02703PlusMidpointP015Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP015Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 3662950203797498560866412024215809971669) * 10^40
        + 8499077303946541352547198550935633640944) * 10^40
        + 1937719896501890542033248011370555116445) * 10^40
        + 396735405870736891478723046043042479143) * 10^40
        + 2392352999126071663869628768941847863184) * 10^40
        + 967992552166946162843052720577485421747) * 10^40
        + 7249323902559112990657862937309980660250) * 10^40
        + 7653881461145913537302569695203919438607) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((31567 * 10^40
        + 4122633138711064628949996459105400361880) * 10^40
        + 9369681832476713311039968691665984729295) * 10^40
        + 6017172108209214621780633943658689558325) * 10^40
        + 9235676906873723410820725394582914058407)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703PlusMidpointP015Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP015BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP015Center2654‖ ≤ batchC02703PlusMidpointP015Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP015Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP015Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP015Input2654 14 =
      (batchC02703PlusMidpointP015Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP015Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP015Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP015Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP015Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP015Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP015Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP015DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP015Factor2654 * embedPair2542
          batchC02703PlusMidpointP015Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP015Factor2654 : ℝ) *
            batchC02703PlusMidpointP015Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP015Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP015Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP015BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP015Factor2654)

def batchC02703PlusMidpointP016Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((965685891782551182861078297 : ℚ) /
        118059162071741130342400000000))

def batchC02703PlusMidpointP016Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP016Factor2654 : RatPair2542 := (((((((((((37190 * 10^40
        + 3415723469630082240793077147587372773358) * 10^40
        + 8099342533899039617319520240131565189622) * 10^40
        + 3117037415168129552398962551496971181855) * 10^40
        + 3957458209265868124952808523345817796313) * 10^40
        + 6829899978347813518277629674157219615705) * 10^40
        + 8248566960027390086314749001059904024562) * 10^40
        + 3244126968757459755740541529594616534135) * 10^40
        + 9828033500425492732550797682411057358223) : ℚ) /
        (((((((69402442539292518693749185058850 * 10^40
        + 166068962871427604147797023136673029041) * 10^40
        + 7454398785356750757113393457363359004290) * 10^40
        + 3793631952020973925100529387682218117759) * 10^40
        + 8679071634027992303145407646978506775442) * 10^40
        + 3063243901909969910060092696263584446817) * 10^40
        + 8016771060756792732981139234894416361576) * 10^40
        + 7812887365489906125539543899723326816256)),
    (((-((((16712 * 10^40
        + 6881955349125675508043610063953192523528) * 10^40
        + 8205190977675966312970687972900774002525) * 10^40
        + 5138753789572684011709702031360256736246) * 10^40
        + 8771400645472892035105928493146944277529)) : ℚ) /
        (((833081283785036900967806832065966613 * 10^40
        + 8751425742414406263446761317992809913658) * 10^40
        + 658889787685572430073369312486930472580) * 10^40
        + 4622675708036533157357890678868341161984)))

noncomputable def batchC02703PlusMidpointP016Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP016BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP016Center2654‖ ≤ batchC02703PlusMidpointP016Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP016Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP016Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP016Input2654 14 =
      (batchC02703PlusMidpointP016Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP016Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP016Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP016Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP016Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP016Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP016Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP016DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP016Factor2654 * embedPair2542
          batchC02703PlusMidpointP016Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP016Factor2654 : ℝ) *
            batchC02703PlusMidpointP016Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP016Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP016Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP016BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP016Factor2654)

def batchC02703PlusMidpointP017Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((2139904379798294298276928491 : ℚ) /
        236118324143482260684800000000))

def batchC02703PlusMidpointP017Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP017Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 3662775267183126518300502662510547007044) * 10^40
        + 3268181204745651242572151668326179459330) * 10^40
        + 4098532733324541564449441132350491076217) * 10^40
        + 5964778535438196710058057938402701098053) * 10^40
        + 6253394020012648231725619917354837763744) * 10^40
        + 4393783856388999763039760519801667712916) * 10^40
        + 7809532858204534639980024345318152513326) * 10^40
        + 6202213564781638699810359395236474018887) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((37034 * 10^40
        + 3555520033300376155134735768636337294473) * 10^40
        + 2578991480077471467933095624472850117358) * 10^40
        + 9165322199103707026937199680171777072100) * 10^40
        + 7474362086605295385486498417921765847787)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703PlusMidpointP017Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP017BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP017Center2654‖ ≤ batchC02703PlusMidpointP017Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP017Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP017Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP017Input2654 14 =
      (batchC02703PlusMidpointP017Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP017Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP017Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP017Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP017Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP017Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP017Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP017DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP017Factor2654 * embedPair2542
          batchC02703PlusMidpointP017Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP017Factor2654 : ℝ) *
            batchC02703PlusMidpointP017Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP017Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP017Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP017BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP017Factor2654)

def batchC02703PlusMidpointP018Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((554686529274626395045879629 : ℚ) /
        59029581035870565171200000000))

def batchC02703PlusMidpointP018Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP018Factor2654 : RatPair2542 := (((((((((((9297 * 10^40
        + 5853920453586278692169131668440967682689) * 10^40
        + 9376788716516867565103227934270331709234) * 10^40
        + 7926788270905533145589571265634377194197) * 10^40
        + 6247238717157787317965565946821482937591) * 10^40
        + 4848684464560928660616780255538551673787) * 10^40
        + 7238634711253401719515002869940369313232) * 10^40
        + 9569965388679011014497467385611627150400) * 10^40
        + 8383009252839391046157632400830702037207) : ℚ) /
        (((((((17350610634823129673437296264712 * 10^40
        + 5041517240717856901036949255784168257260) * 10^40
        + 4363599696339187689278348364340839751072) * 10^40
        + 5948407988005243481275132346920554529439) * 10^40
        + 9669767908506998075786351911744626693860) * 10^40
        + 5765810975477492477515023174065896111704) * 10^40
        + 4504192765189198183245284808723604090394) * 10^40
        + 1953221841372476531384885974930831704064)),
    (((-((((9599 * 10^40
        + 7084444490616077083378163277896029257400) * 10^40
        + 6720487859975874229910191183953125271840) * 10^40
        + 3372974976462596737642709889203204298901) * 10^40
        + 3379076160429163450049074373059413631053)) : ℚ) /
        (((416540641892518450483903416032983306 * 10^40
        + 9375712871207203131723380658996404956829) * 10^40
        + 329444893842786215036684656243465236290) * 10^40
        + 2311337854018266578678945339434170580992)))

noncomputable def batchC02703PlusMidpointP018Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP018BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP018Center2654‖ ≤ batchC02703PlusMidpointP018Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP018Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP018Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP018Input2654 14 =
      (batchC02703PlusMidpointP018Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP018Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP018Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP018Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP018Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP018Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP018Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP018DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP018Factor2654 * embedPair2542
          batchC02703PlusMidpointP018Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP018Factor2654 : ℝ) *
            batchC02703PlusMidpointP018Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP018Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP018Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP018BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP018Factor2654)

def batchC02703PlusMidpointP019Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((118061729677797542810828703 : ℚ) /
        11805916207174113034240000000))

def batchC02703PlusMidpointP019Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP019Factor2654 : RatPair2542 := (((((((((((9297 * 10^40
        + 5853914755289053455350440028772720174311) * 10^40
        + 8529513288059794070605877876705208168822) * 10^40
        + 1773172191640373893167564278190848014025) * 10^40
        + 4050585345857904547272419405722523392622) * 10^40
        + 9840825756268889753032580864746845167247) * 10^40
        + 2877546662476958967388991228192820624071) * 10^40
        + 3734973530969722953936397579024000418642) * 10^40
        + 6578269080802214970696193945193332829991) : ℚ) /
        (((((((17350610634823129673437296264712 * 10^40
        + 5041517240717856901036949255784168257260) * 10^40
        + 4363599696339187689278348364340839751072) * 10^40
        + 5948407988005243481275132346920554529439) * 10^40
        + 9669767908506998075786351911744626693860) * 10^40
        + 5765810975477492477515023174065896111704) * 10^40
        + 4504192765189198183245284808723604090394) * 10^40
        + 1953221841372476531384885974930831704064)),
    (((-((((329 * 10^40
        + 5549780732297202896079744852947433642457) * 10^40
        + 1496449842541208943914122865546986420709) * 10^40
        + 8054498138661110292285413468090390684442) * 10^40
        + 6585599049241864098380992951740655971205)) : ℚ) /
        (((13436794899758659693029142452676880 * 10^40
        + 8689539124877651713926560666419238869575) * 10^40
        + 1300949835285251168226989827620756943106) * 10^40
        + 1364881866258653760602546623852715180032)))

noncomputable def batchC02703PlusMidpointP019Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP019BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP019Center2654‖ ≤ batchC02703PlusMidpointP019Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP019Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP019Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP019Input2654 14 =
      (batchC02703PlusMidpointP019Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP019Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP019Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP019Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP019Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP019Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP019Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP019DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP019Factor2654 * embedPair2542
          batchC02703PlusMidpointP019Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP019Factor2654 : ℝ) *
            batchC02703PlusMidpointP019Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP019Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP019Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP019BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP019Factor2654)

def batchC02703PlusMidpointP020Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((2516179419352937322532008027 : ℚ) /
        236118324143482260684800000000))

def batchC02703PlusMidpointP020Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP020Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 3662530502988387469256762392321134298207) * 10^40
        + 2592934152639573570133826340174664037698) * 10^40
        + 9236268825348010427321755795387423650946) * 10^40
        + 3595380371270611373311295415459191561367) * 10^40
        + 4771766197298699405589436004116169325201) * 10^40
        + 1244215802519086836935848277926358038857) * 10^40
        + 6442557900125675259157006438640574445404) * 10^40
        + 2343197631372271752924793284229434688935) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((43546 * 10^40
        + 3771786538995338908760045842519459836840) * 10^40
        + 59364077469969192175242524658879277351) * 10^40
        + 8592466619747835731613137444635232647910) * 10^40
        + 6918482630601370460671604554934149986139)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703PlusMidpointP020Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP020BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP020Center2654‖ ≤ batchC02703PlusMidpointP020Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP020Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP020Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP020Input2654 14 =
      (batchC02703PlusMidpointP020Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP020Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP020Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP020Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP020Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP020Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP020Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP020DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP020Factor2654 * embedPair2542
          batchC02703PlusMidpointP020Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP020Factor2654 : ℝ) *
            batchC02703PlusMidpointP020Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP020Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP020Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP020BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP020Factor2654)

def batchC02703PlusMidpointP021Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((2645486933342248857784813371 : ℚ) /
        236118324143482260684800000000))

def batchC02703PlusMidpointP021Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP021Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 3662437255878493923049818778515155084991) * 10^40
        + 5279134898816774086417438031600986371127) * 10^40
        + 5957861173940614396219630159190106230353) * 10^40
        + 4086147778907709904850138903252464477809) * 10^40
        + 3254445211127679123278219297693856044351) * 10^40
        + 2146187286025248889020141949987871420022) * 10^40
        + 3467274070801570260800349293382812587445) * 10^40
        + 9885685338447214607582133460630173433447) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((1476 * 10^40
        + 9110882755020876244388725328415739796845) * 10^40
        + 4638080511657621807003558548127578807591) * 10^40
        + 3708235756616031949188742967829672273757) * 10^40
        + 545106025169968103504557099457577524837)) : ℚ) /
        (((53747179599034638772116569810707523 * 10^40
        + 4758156499510606855706242665676955478300) * 10^40
        + 5203799341141004672907959310483027772424) * 10^40
        + 5459527465034615042410186495410860720128)))

noncomputable def batchC02703PlusMidpointP021Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP021BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP021Center2654‖ ≤ batchC02703PlusMidpointP021Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP021Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP021Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP021Input2654 14 =
      (batchC02703PlusMidpointP021Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP021Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP021Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP021Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP021Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP021Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP021Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP021DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP021Factor2654 * embedPair2542
          batchC02703PlusMidpointP021Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP021Factor2654 : ℝ) *
            batchC02703PlusMidpointP021Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP021Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP021Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP021BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP021Factor2654)

def batchC02703PlusMidpointP022Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((542334257496525531427714089 : ℚ) /
        47223664828696452136960000000))

def batchC02703PlusMidpointP022Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP022Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 3662387720954867339373742868446068323662) * 10^40
        + 8972291958351506490219939756520039671420) * 10^40
        + 2261125764972492991528651490093044139273) * 10^40
        + 5080717890517031515996722336163743435655) * 10^40
        + 1896907579807531190208242508928397191196) * 10^40
        + 3436431675655049969929610414740832763920) * 10^40
        + 5760690336114158939135970636163323324511) * 10^40
        + 4851720777783092542029236000619896003031) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((46929 * 10^40
        + 6663668010488072518582102966513532721267) * 10^40
        + 3117358151645439526939584701464549884537) * 10^40
        + 1607025008891388867866451853174458653641) * 10^40
        + 6149008276967601599493299500030293116365)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703PlusMidpointP022Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP022BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP022Center2654‖ ≤ batchC02703PlusMidpointP022Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP022Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP022Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP022Input2654 14 =
      (batchC02703PlusMidpointP022Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP022Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP022Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP022Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP022Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP022Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP022Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP022DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP022Factor2654 * embedPair2542
          batchC02703PlusMidpointP022Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP022Factor2654 : ℝ) *
            batchC02703PlusMidpointP022Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP022Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP022Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP022BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP022Factor2654)

def batchC02703PlusMidpointP023Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1451246539493341798322821389 : ℚ) /
        118059162071741130342400000000))

def batchC02703PlusMidpointP023Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP023Factor2654 : RatPair2542 := (((((((((((37190 * 10^40
        + 3415559512736742942010827755424486834460) * 10^40
        + 2293848664556512742418936266241713449687) * 10^40
        + 2699757723702585193251199242170960933260) * 10^40
        + 9949695317821607632430980415534111453796) * 10^40
        + 1292961223606703752559190405921744625237) * 10^40
        + 845000983278917101925216508243538549577) * 10^40
        + 734166111646156593517877589402967414017) * 10^40
        + 9148881621353697116935276221254790830935) : ℚ) /
        (((((((69402442539292518693749185058850 * 10^40
        + 166068962871427604147797023136673029041) * 10^40
        + 7454398785356750757113393457363359004290) * 10^40
        + 3793631952020973925100529387682218117759) * 10^40
        + 8679071634027992303145407646978506775442) * 10^40
        + 3063243901909969910060092696263584446817) * 10^40
        + 8016771060756792732981139234894416361576) * 10^40
        + 7812887365489906125539543899723326816256)),
    (((-((((25116 * 10^40
        + 663273547374973823063841962297767683925) * 10^40
        + 5475978788976751083713272361223057356840) * 10^40
        + 6987310810790175920291608568046684963487) * 10^40
        + 8731174245438091965924950025945564879373)) : ℚ) /
        (((833081283785036900967806832065966613 * 10^40
        + 8751425742414406263446761317992809913658) * 10^40
        + 658889787685572430073369312486930472580) * 10^40
        + 4622675708036533157357890678868341161984)))

noncomputable def batchC02703PlusMidpointP023Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP023BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP023Center2654‖ ≤ batchC02703PlusMidpointP023Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP023Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP023Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP023Input2654 14 =
      (batchC02703PlusMidpointP023Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP023Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP023Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP023Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP023Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP023Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP023Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP023DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP023Factor2654 * embedPair2542
          batchC02703PlusMidpointP023Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP023Factor2654 : ℝ) *
            batchC02703PlusMidpointP023Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP023Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP023Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP023BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP023Factor2654)

def batchC02703PlusMidpointP024Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1495093523437065373217234451 : ℚ) /
        118059162071741130342400000000))

def batchC02703PlusMidpointP024Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP024Factor2654 : RatPair2542 := (((((((((((37190 * 10^40
        + 3415541464104916857171623400813113919292) * 10^40
        + 4258011722927899157018483080312358341669) * 10^40
        + 2789586352265003372523394022459218460018) * 10^40
        + 8642995031492280604401411313432518200519) * 10^40
        + 6471101040839540076147479886414934292295) * 10^40
        + 1737582393903266029674162398826020817857) * 10^40
        + 3712352189275549123825575012713167190972) * 10^40
        + 3384332413519576038736196981631257637015) : ℚ) /
        (((((((69402442539292518693749185058850 * 10^40
        + 166068962871427604147797023136673029041) * 10^40
        + 7454398785356750757113393457363359004290) * 10^40
        + 3793631952020973925100529387682218117759) * 10^40
        + 8679071634027992303145407646978506775442) * 10^40
        + 3063243901909969910060092696263584446817) * 10^40
        + 8016771060756792732981139234894416361576) * 10^40
        + 7812887365489906125539543899723326816256)),
    (((-((((25874 * 10^40
        + 9062122508571899026236923449236865909797) * 10^40
        + 5218788762954467220486759538105097357215) * 10^40
        + 9948937051732193191462623499115102434982) * 10^40
        + 4100254252612460919843622445115352415507)) : ℚ) /
        (((833081283785036900967806832065966613 * 10^40
        + 8751425742414406263446761317992809913658) * 10^40
        + 658889787685572430073369312486930472580) * 10^40
        + 4622675708036533157357890678868341161984)))

noncomputable def batchC02703PlusMidpointP024Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP024BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP024Center2654‖ ≤ batchC02703PlusMidpointP024Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP024Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP024Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP024Input2654 14 =
      (batchC02703PlusMidpointP024Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP024Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP024Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP024Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP024Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP024Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP024Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP024DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP024Factor2654 * embedPair2542
          batchC02703PlusMidpointP024Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP024Factor2654 : ℝ) *
            batchC02703PlusMidpointP024Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP024Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP024Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP024BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP024Factor2654)

def batchC02703PlusMidpointP025Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((48439674860800074916295889 : ℚ) /
        3689348814741910323200000000))

def batchC02703PlusMidpointP025Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP025Factor2654 : RatPair2542 := (((((((((((36 * 10^40
        + 3186929216870519203014731023131205260103) * 10^40
        + 414073866506548200255082301302418776428) * 10^40
        + 4533974158393951917530075822879279350077) * 10^40
        + 4783554309954433304854392507756728959267) * 10^40
        + 2890293174573332720135778249288975059431) * 10^40
        + 9861493615294815130634794289808635070258) * 10^40
        + 5529303581037381360705796683505880854473) * 10^40
        + 4091367043773337919573279768646481978207) : ℚ) /
        (((((((67775822792277850286864438534 * 10^40
        + 332193426721554128519675583030406907254) * 10^40
        + 9235795311313824951911243548298206405277) * 10^40
        + 6273235968703145482348730985730158416130) * 10^40
        + 6248710030892605461233540437155252448022) * 10^40
        + 8928772699122958954990293059273694906686) * 10^40
        + 3455094502989020305403301893784076578478) * 10^40
        + 1023254772817861236450722210839573561344)),
    (((-((((838 * 10^40
        + 3235057387947486577401457028437231660994) * 10^40
        + 33121750423102308349385024348838410960) * 10^40
        + 9989893904970005416578761791675398805467) * 10^40
        + 4322653731235859075390171677533627025873)) : ℚ) /
        (((26033790118282403155243963502061456 * 10^40
        + 6835982054450450195732711291187275309801) * 10^40
        + 8145590305865174138439792791015216577268) * 10^40
        + 1394458615876141661167434083714635661312)))

noncomputable def batchC02703PlusMidpointP025Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP025BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP025Center2654‖ ≤ batchC02703PlusMidpointP025Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP025Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP025Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP025Input2654 14 =
      (batchC02703PlusMidpointP025Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP025Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP025Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP025Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP025Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP025Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP025Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP025DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP025Factor2654 * embedPair2542
          batchC02703PlusMidpointP025Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP025Factor2654 : ℝ) *
            batchC02703PlusMidpointP025Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP025Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP025Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP025BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP025Factor2654)

def batchC02703PlusMidpointP026Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((100390806713240309485743021 : ℚ) /
        7378697629483820646400000000))

def batchC02703PlusMidpointP026Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP026Factor2654 : RatPair2542 := (((((((((((145 * 10^40
        + 2747716770705460843276038862307905690833) * 10^40
        + 7530416038940185467596222961292010869833) * 10^40
        + 8633487883111487595139235021134145586369) * 10^40
        + 8471148086479160147493947789817060449215) * 10^40
        + 4339888478180787928486402941588471210858) * 10^40
        + 7478445575208205971086099425305620051560) * 10^40
        + 7585887566531313319765363682008678502075) * 10^40
        + 6315717196352871396517988362179967341335) : ℚ) /
        (((((((271103291169111401147457754136 * 10^40
        + 1328773706886216514078702332121627629019) * 10^40
        + 6943181245255299807644974193192825621110) * 10^40
        + 5092943874812581929394923942920633664522) * 10^40
        + 4994840123570421844934161748621009792091) * 10^40
        + 5715090796491835819961172237094779626745) * 10^40
        + 3820378011956081221613207575136306313912) * 10^40
        + 4093019091271444945802888843358294245376)),
    (((-((((1737 * 10^40
        + 4182066588562201254512192660865959743180) * 10^40
        + 6380638376666734876580277844597327087358) * 10^40
        + 2909718141305567349410806948420122983116) * 10^40
        + 9799933547457364167397916034606215629997)) : ℚ) /
        (((52067580236564806310487927004122913 * 10^40
        + 3671964108900900391465422582374550619603) * 10^40
        + 6291180611730348276879585582030433154536) * 10^40
        + 2788917231752283322334868167429271322624)))

noncomputable def batchC02703PlusMidpointP026Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP026BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP026Center2654‖ ≤ batchC02703PlusMidpointP026Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP026Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP026Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP026Input2654 14 =
      (batchC02703PlusMidpointP026Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP026Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP026Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP026Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP026Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP026Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP026Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP026DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP026Factor2654 * embedPair2542
          batchC02703PlusMidpointP026Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP026Factor2654 : ℝ) *
            batchC02703PlusMidpointP026Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP026Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP026Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP026BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP026Factor2654)

def batchC02703PlusMidpointP027Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((210915907231581076143804291 : ℚ) /
        14757395258967641292800000000))

def batchC02703PlusMidpointP027Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP027Factor2654 : RatPair2542 := (((((((((((581 * 10^40
        + 990866499922680274438026811309291281577) * 10^40
        + 1008570625512988561069864564656274024979) * 10^40
        + 518704493321514208979019505354124507623) * 10^40
        + 4151883508319089336659924702981417391514) * 10^40
        + 5446725795473434636922710647407081017634) * 10^40
        + 6745536988803744188121471614073052786370) * 10^40
        + 9147010128951128710836131448456804742508) * 10^40
        + 6159628960317725155946071896711305103607) : ℚ) /
        (((((((1084413164676445604589831016544 * 10^40
        + 5315094827544866056314809328486510516078) * 10^40
        + 7772724981021199230579896772771302484442) * 10^40
        + 371775499250327717579695771682534658089) * 10^40
        + 9979360494281687379736646994484039168366) * 10^40
        + 2860363185967343279844688948379118506981) * 10^40
        + 5281512047824324886452830300545225255649) * 10^40
        + 6372076365085779783211555373433176981504)),
    (((-((((3650 * 10^40
        + 2260445506426510016038988560645839921491) * 10^40
        + 1069169155704016824774456493748723055765) * 10^40
        + 5188700606641451740872755612819927422511) * 10^40
        + 4955216290333309201799840070401586208387)) : ℚ) /
        (((104135160473129612620975854008245826 * 10^40
        + 7343928217801800782930845164749101239207) * 10^40
        + 2582361223460696553759171164060866309072) * 10^40
        + 5577834463504566644669736334858542645248)))

noncomputable def batchC02703PlusMidpointP027Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP027BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP027Center2654‖ ≤ batchC02703PlusMidpointP027Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP027Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP027Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP027Input2654 14 =
      (batchC02703PlusMidpointP027Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP027Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP027Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP027Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP027Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP027Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP027Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP027DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP027Factor2654 * embedPair2542
          batchC02703PlusMidpointP027Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP027Factor2654 : ℝ) *
            batchC02703PlusMidpointP027Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP027Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP027Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP027BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP027Factor2654)

def batchC02703PlusMidpointP028Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((859712854308450190152717591 : ℚ) /
        59029581035870565171200000000))

def batchC02703PlusMidpointP028Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP028Factor2654 : RatPair2542 := (((((((((((9297 * 10^40
        + 5853860179439671360917224850390163578024) * 10^40
        + 6116249786762120126426306612512201413818) * 10^40
        + 7366722223261891973399792808947045027439) * 10^40
        + 7821932132143511088445634972210861408539) * 10^40
        + 8971653144877244370176198721467155423633) * 10^40
        + 8475850234361445747436828973168158875733) * 10^40
        + 6536057403904645754152742582460205815820) * 10^40
        + 689267532529551410767432872475491044847) : ℚ) /
        (((((((17350610634823129673437296264712 * 10^40
        + 5041517240717856901036949255784168257260) * 10^40
        + 4363599696339187689278348364340839751072) * 10^40
        + 5948407988005243481275132346920554529439) * 10^40
        + 9669767908506998075786351911744626693860) * 10^40
        + 5765810975477492477515023174065896111704) * 10^40
        + 4504192765189198183245284808723604090394) * 10^40
        + 1953221841372476531384885974930831704064)),
    (((-((((14878 * 10^40
        + 6608502983170789388981466409845403381621) * 10^40
        + 861077185117093416496181277822283206572) * 10^40
        + 8764631251387617555928184058189190945925) * 10^40
        + 3510948187236902886659766884403670206487)) : ℚ) /
        (((416540641892518450483903416032983306 * 10^40
        + 9375712871207203131723380658996404956829) * 10^40
        + 329444893842786215036684656243465236290) * 10^40
        + 2311337854018266578678945339434170580992)))

noncomputable def batchC02703PlusMidpointP028Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP028BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP028Center2654‖ ≤ batchC02703PlusMidpointP028Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP028Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP028Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP028Input2654 14 =
      (batchC02703PlusMidpointP028Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP028Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP028Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP028Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP028Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP028Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP028Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP028DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP028Factor2654 * embedPair2542
          batchC02703PlusMidpointP028Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP028Factor2654 : ℝ) *
            batchC02703PlusMidpointP028Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP028Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP028Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP028BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP028Factor2654)

def batchC02703PlusMidpointP029Input2654 : RatPair2542 := ((((-((2313160 * 10^40
        + 5214482642262302165375039614491430160787) * 10^40
        + 5464429790672906586333542102438591055953)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((884146769519556836563855947 : ℚ) /
        59029581035870565171200000000))

def batchC02703PlusMidpointP029Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703PlusMidpointP029Factor2654 : RatPair2542 := (((((((((((9297 * 10^40
        + 5853854226571373472853608864502897440762) * 10^40
        + 8114487205392256837207265759564175744632) * 10^40
        + 5670617114435219816088958494925829046041) * 10^40
        + 2101046804825196754258678620297758846863) * 10^40
        + 9224835515776209589400598623327565635711) * 10^40
        + 3340180488412801776530204821655659874810) * 10^40
        + 1865695862499118106771020525370159638567) * 10^40
        + 7187554076640862183158618397519082656775) : ℚ) /
        (((((((17350610634823129673437296264712 * 10^40
        + 5041517240717856901036949255784168257260) * 10^40
        + 4363599696339187689278348364340839751072) * 10^40
        + 5948407988005243481275132346920554529439) * 10^40
        + 9669767908506998075786351911744626693860) * 10^40
        + 5765810975477492477515023174065896111704) * 10^40
        + 4504192765189198183245284808723604090394) * 10^40
        + 1953221841372476531384885974930831704064)),
    (((-((((15301 * 10^40
        + 5275503239138642032810727348017658280548) * 10^40
        + 1356021969040571585064950270818568534767) * 10^40
        + 2616435372477613328199928174455994195039) * 10^40
        + 2084701635634558236637234627119608373579)) : ℚ) /
        (((416540641892518450483903416032983306 * 10^40
        + 9375712871207203131723380658996404956829) * 10^40
        + 329444893842786215036684656243465236290) * 10^40
        + 2311337854018266578678945339434170580992)))

noncomputable def batchC02703PlusMidpointP029Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703PlusMidpointP029BaseError2654 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP029Center2654‖ ≤ batchC02703PlusMidpointP029Error2654
          := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703PlusMidpointP029Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703PlusMidpointP029Input2654]
  have hs : compactExp2547 batchC02703PlusMidpointP029Input2654 14 =
      (batchC02703PlusMidpointP029Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703PlusMidpointP029Input2654 14).2 : ℝ) =
      batchC02703PlusMidpointP029Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703PlusMidpointP029Error2654]
  have h := compactExp_error2547 batchC02703PlusMidpointP029Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      batchC02703PlusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703PlusMidpointP029Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703PlusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703PlusMidpointP029Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703PlusMidpointP029DerivativeError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP029Factor2654 * embedPair2542
          batchC02703PlusMidpointP029Center2654‖ ≤
        (pairMagnitude2542 batchC02703PlusMidpointP029Factor2654 : ℝ) *
            batchC02703PlusMidpointP029Error2654 := by
  have hx : |batchC02703PlusMidpointPosition2654| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC02703PlusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchC02703PlusMidpointPosition2654 = embedPair2542
          batchC02703PlusMidpointP029Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703PlusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703PlusMidpointP029Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703PlusMidpointP029BaseError2654
    (embedPair_magnitude2542 batchC02703PlusMidpointP029Factor2654)

theorem batchC02703PlusMidpointGrid2654 :
    -stripRadius2303 + ((5407 : ℝ) /
        2) * (2 * stripRadius2303 / 10240) =
      batchC02703PlusMidpointPosition2654 := by
  norm_num [stripRadius2303, batchC02703PlusMidpointPosition2654]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP000DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP001DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP002DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP003DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP004DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP005DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP006DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP007DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP008DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP009DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP010DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP011DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP012DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP013DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP014DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP015DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP016DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP017DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP018DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP019DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP020DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP021DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP022DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP023DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP024DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP025DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP026DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP027DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP028DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointP029DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusMidpointGrid2654
