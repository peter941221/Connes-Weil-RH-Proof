import ConnesWeilRH.Dev.C1RouteANodeExpN02705Plus2577

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def nodeJet2N02705PlusPointPosition2577 : ℝ := (((-31653888483) : ℝ) /
        10240000000)

theorem nodeJet2N02705PlusPointZero2577 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def nodeJet2N02705PlusPointP000Center2577 : RatPair2542 := (0, 0)

def nodeJet2N02705PlusPointP000Factor2577 : RatPair2542 := (0, 0)

noncomputable def nodeJet2N02705PlusPointP000Error2577 : ℝ := 0

theorem nodeJet2N02705PlusPointP000Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02705PlusPointPosition2577 = 0 := by
  exact nodeExpN02705PlusPointP000Exterior2577 n

theorem nodeJet2N02705PlusPointP000BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP000Center2577‖ ≤ nodeJet2N02705PlusPointP000Error2577
          := by
  exact nodeExpN02705PlusPointP000BaseError2577

theorem nodeJet2N02705PlusPointP000DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP000Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP000Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP000Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP000Error2577 := by
  rw [nodeJet2N02705PlusPointP000Exterior2577]
  norm_num [nodeJet2N02705PlusPointP000Factor2577, nodeJet2N02705PlusPointP000Center2577,
      nodeJet2N02705PlusPointP000Error2577,
      nodeJet2N02705PlusPointZero2577, pairMagnitude2542]

def nodeJet2N02705PlusPointP001Input2577 : RatPair2542 :=
    ((((-(3023607753986956922918087616536546748773 *
    10^40
        + 6838956371435611813009672146364574867683)) : ℚ) /
        (8511279604154028674011082907130390598740 * 10^40
        + 8004112173150622382000883902709760000000)),
    ((174865292075716174968560007 : ℚ) /
        737869762948382064640000000))

def nodeJet2N02705PlusPointP001Center2577 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP001Factor2577 : RatPair2542 := ((((((((((2897272703908237252177 *
    10^40
        + 3212378516451687860214747426011903325818) * 10^40
        + 743542453681293994933230419972144059262) * 10^40
        + 6244684489131090145061654374546683177436) * 10^40
        + 5509702524551355871136381861052381523104) * 10^40
        + 2606593000392910735078347900385591777864) * 10^40
        + 3293013371592711625248681578076308512513) * 10^40
        + 3057663425464676476484931190488312180055) : ℚ) /
        (((((((8598038200957472 * 10^40
        + 141790292102205354197806213013410962041) * 10^40
        + 1621595586686419268366832641327035700902) * 10^40
        + 8644107106818903029834864907366570427723) * 10^40
        + 2966182222028762433558068143872846920503) * 10^40
        + 9256141228727664788448559272500972010992) * 10^40
        + 8780447658410284346885802049043658572913) * 10^40
        + 8024020628939428337850636823283560873984)),
    (((-(((426011029297309647821739117585347 * 10^40
        + 7879964829223088498519322986912149849186) * 10^40
        + 7241357351690246976113748225896419630649) * 10^40
        + 7409984821464096464611080171935381417229)) : ℚ) /
        (((9272560704011309957005710651 * 10^40
        + 8069058291469678712499426532598938186360) * 10^40
        + 2264379892714596108919112878838923781865) * 10^40
        + 733434366566606583015219610970623049728)))

noncomputable def nodeJet2N02705PlusPointP001Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP001BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP001Center2577‖ ≤ nodeJet2N02705PlusPointP001Error2577
          := by
  exact nodeExpN02705PlusPointP001BaseError2577

theorem nodeJet2N02705PlusPointP001DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP001Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP001Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP001Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP001Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP001Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP001Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP001BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP001Factor2577)

def nodeJet2N02705PlusPointP002Input2577 : RatPair2542 :=
    ((((-(1638859412615474757001081566597964099486 *
    10^40
        + 4331734993860018146222766991230985822547)) : ℚ) /
        (6677151314258110391825028471093402075161 * 10^40
        + 8148315816099404395428715739217920000000)),
    (((-174865292075716174968560007) : ℚ) /
        368934881474191032320000000))

def nodeJet2N02705PlusPointP002Center2577 : RatPair2542 := ((((-283269467081739495401) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-697336509513847197747) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def nodeJet2N02705PlusPointP002Factor2577 : RatPair2542 := ((((((((((7394955317100848778 * 10^40
        + 7521821553581166220506236108200847797986) * 10^40
        + 7181398049930608420523419825414767727529) * 10^40
        + 5420152830898277520933069186470257948577) * 10^40
        + 6536437271981924432374857568472894038110) * 10^40
        + 719835374019962973583063447997495789230) * 10^40
        + 9733676995396195913369086318126511148728) * 10^40
        + 3672735024341099377422433686570657464855) : ℚ) /
        (((((((52108046783186561 * 10^40
        + 2517301206754568672051708514103298778758) * 10^40
        + 307278298735271599409957052881096749749) * 10^40
        + 8912157885642591946906725677832695378712) * 10^40
        + 5349668788316479638210476901573947197792) * 10^40
        + 3477780095469449440409070908119974740958) * 10^40
        + 6649761686748851669514236472658946305194) * 10^40
        + 1263766961113092385263524678550866100224)),
    (((((75006479694308303401830293841719 * 10^40
        + 6245432631861624566262210490074374801737) * 10^40
        + 4765471464824733126915169569137004212531) * 10^40
        + 2864404235227870409134019196644895631149) : ℚ) /
        (((22827187032831391170524010701 * 10^40
        + 8575416780773630581938393274919168558414) * 10^40
        + 3060834003913784083951889723658255416479) * 10^40
        + 9528788458481189921638234054314235527168)))

noncomputable def nodeJet2N02705PlusPointP002Error2577 : ℝ := ((715960097493195589 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem nodeJet2N02705PlusPointP002BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP002Center2577‖ ≤ nodeJet2N02705PlusPointP002Error2577
          := by
  exact nodeExpN02705PlusPointP002BaseError2577

theorem nodeJet2N02705PlusPointP002DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP002Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP002Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP002Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP002Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP002Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP002Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP002BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP002Factor2577)

def nodeJet2N02705PlusPointP003Input2577 : RatPair2542 := ((((-((589 * 10^40
        + 7228286059281175019250523115978507539176) * 10^40
        + 7815277842486084277325670743963551945163)) : ℚ) /
        ((3259 * 10^40
        + 8976654890313777338921755240451858920673) * 10^40
        + 3765349097629268219761063158087680000000)),
    (((-174865292075716174968560007) : ℚ) /
        368934881474191032320000000))

def nodeJet2N02705PlusPointP003Center2577 : RatPair2542 := ((((-2122071398865999455084083525) : ℚ)
    /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-10447987052535926618002489217) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def nodeJet2N02705PlusPointP003Factor2577 : RatPair2542 :=
    ((((-(((((((39573157953935207391641044939139435 *
    10^40
        + 9806345240412918957409911833478271495551) * 10^40
        + 5065446236775790141015572515500861975172) * 10^40
        + 9233345103775319149970651678713609646136) * 10^40
        + 4776846572231330356019537766759608263256) * 10^40
        + 5410113633538149764735536084861442910025) * 10^40
        + 7835824221416347376190336164301418383870) * 10^40
        + 7640071930868561463882080707237775188745)) : ℚ) /
        (((((((29604367698943771981708558977030 * 10^40
        + 9750626296738597542654141573367848536409) * 10^40
        + 6952446126917018946733924115648897938036) * 10^40
        + 2756621396728156120213212379139513240729) * 10^40
        + 8875828780001173777272969283944059597379) * 10^40
        + 1062944108982617242874876149987906172642) * 10^40
        + 1952814561977408250195797687281132808703) * 10^40
        + 8022754047778734387929287440564217708544)),
    (((((630253101132622743152811258029675445894 * 10^40
        + 5385078643487812743884246781012994360645) * 10^40
        + 4016562341441545328199450590455588706656) * 10^40
        + 4096231162582829321724611436000832778109) : ℚ) /
        (((544098958820394839962216851308212164 * 10^40
        + 4830094983735407052937641969332998957692) * 10^40
        + 6570814641536834032655487643959894692813) * 10^40
        + 1609016050185404464549032956900187045888)))

noncomputable def nodeJet2N02705PlusPointP003Error2577 : ℝ := ((40226203768278363825291287 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP003BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP003Center2577‖ ≤ nodeJet2N02705PlusPointP003Error2577
          := by
  exact nodeExpN02705PlusPointP003BaseError2577

theorem nodeJet2N02705PlusPointP003DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP003Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP003Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP003Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP003Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP003Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP003Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP003BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP003Factor2577)

def nodeJet2N02705PlusPointP004Input2577 : RatPair2542 := ((((-((18 * 10^40
        + 6932674971925147917508549558213400347396) * 10^40
        + 486924668160436812400090012701117804803)) : ℚ) /
        ((119 * 10^40
        + 2496410941960060508819208543369047417438) * 10^40
        + 2834992468434524816007071221678080000000)),
    ((174865292075716174968560007 : ℚ) /
        368934881474191032320000000))

def nodeJet2N02705PlusPointP004Center2577 : RatPair2542 := ((((-2052089403884525222829097911721) :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((2525857934597415579677892312545 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def nodeJet2N02705PlusPointP004Factor2577 : RatPair2542 :=
    ((((-(((((((78843183547619303636661352047 * 10^40
        + 884623765207428039225219215043606638977) * 10^40
        + 9306520422126980726634893061909967723774) * 10^40
        + 2343067554593242745746856914086783794375) * 10^40
        + 7371274598657782850221813735835731933156) * 10^40
        + 723474823806720816240261771039382490834) * 10^40
        + 4451128756661509019326915132380711764155) * 10^40
        + 5851296513519537615623716033369696431145)) : ℚ) /
        (((((((53011274345890175698472415 * 10^40
        + 6654196183038584089428426414779223849907) * 10^40
        + 7432821288974638103849279611788523908928) * 10^40
        + 4001249450104118954482731842358523964473) * 10^40
        + 4525496761622166743752808507278718631827) * 10^40
        + 7860437450765645771850202732544696646713) * 10^40
        + 2817322538080545719004856834432560587189) * 10^40
        + 7397138783410592076845762711445437415424)),
    (((-(((436878116687272275317128410438456901 * 10^40
        + 5460339862433687697514754969316055032848) * 10^40
        + 1917965421402210189022455558382512025741) * 10^40
        + 3164237915586678418091687322128785388749)) : ℚ) /
        (((728088417336041513946925114699671 * 10^40
        + 6448650525065914750459888068963248539818) * 10^40
        + 4842754602194513589572666504736055075634) * 10^40
        + 8419119820800285945050012408479500730368)))

noncomputable def nodeJet2N02705PlusPointP004Error2577 : ℝ := ((4746455199159367328887253045 : ℝ)
    /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem nodeJet2N02705PlusPointP004BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP004Center2577‖ ≤ nodeJet2N02705PlusPointP004Error2577
          := by
  exact nodeExpN02705PlusPointP004BaseError2577

theorem nodeJet2N02705PlusPointP004DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP004Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP004Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP004Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP004Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP004Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP004Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP004BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP004Factor2577)

def nodeJet2N02705PlusPointP005Center2577 : RatPair2542 := (0, 0)

def nodeJet2N02705PlusPointP005Factor2577 : RatPair2542 := (0, 0)

noncomputable def nodeJet2N02705PlusPointP005Error2577 : ℝ := 0

theorem nodeJet2N02705PlusPointP005Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02705PlusPointPosition2577 = 0 := by
  exact nodeExpN02705PlusPointP005Exterior2577 n

theorem nodeJet2N02705PlusPointP005BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP005Center2577‖ ≤ nodeJet2N02705PlusPointP005Error2577
          := by
  exact nodeExpN02705PlusPointP005BaseError2577

theorem nodeJet2N02705PlusPointP005DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP005Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP005Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP005Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP005Error2577 := by
  rw [nodeJet2N02705PlusPointP005Exterior2577]
  norm_num [nodeJet2N02705PlusPointP005Factor2577, nodeJet2N02705PlusPointP005Center2577,
      nodeJet2N02705PlusPointP005Error2577,
      nodeJet2N02705PlusPointZero2577, pairMagnitude2542]

def nodeJet2N02705PlusPointP006Input2577 : RatPair2542 := ((((-1052182359368453146349943998425413)
    : ℚ) /
        1771445797272420243763363840000000),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP006Center2577 : RatPair2542 := (((700265187724743 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP006Factor2577 : RatPair2542 := (((((41846745 * 10^40
        + 3103802903985477053825805763067158453462) * 10^40
        + 5544178144676864314484412046433543073441) : ℚ) /
        ((8340 * 10^40
        + 8781515554826815851359804479075949211870) * 10^40
        + 2087085281107477737937648185734172293764)),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP006Error2577 : ℝ := ((1278008009571 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeJet2N02705PlusPointP006BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP006Center2577‖ ≤ nodeJet2N02705PlusPointP006Error2577
          := by
  exact nodeExpN02705PlusPointP006BaseError2577

theorem nodeJet2N02705PlusPointP006DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP006Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP006Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP006Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP006Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP006Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP006Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP006BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP006Factor2577)

def nodeJet2N02705PlusPointP007Input2577 : RatPair2542 := ((((-((589 * 10^40
        + 7228286059281175019250523115978507539176) * 10^40
        + 7815277842486084277325670743963551945163)) : ℚ) /
        ((814 * 10^40
        + 9744163722578444334730438810112964730168) * 10^40
        + 3441337274407317054940265789521920000000)),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP007Center2577 : RatPair2542 := (((11277108740164686308975014741 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP007Factor2577 : RatPair2542 := ((((((((((1219750 * 10^40
        + 3751918207729638175082520291128241634073) * 10^40
        + 7440533724547347081844552774089737786137) * 10^40
        + 5421041069091191069152431026507499483012) * 10^40
        + 7982652626716096232099828612087509566928) * 10^40
        + 7965794444790384840771160536586022080747) * 10^40
        + 4809959845248946072973567045801340454893) * 10^40
        + 1326556379030219196256950393112589401441) : ℚ) /
        (((((((5978 * 10^40
        + 5544451800233632820430742636911568795351) * 10^40
        + 5013096037731222883930865390245520989662) * 10^40
        + 8035436923110592587122265602624292446791) * 10^40
        + 225492355137801418421181923934139379379) * 10^40
        + 1632001303390110722238321314595919717869) * 10^40
        + 12039448580981825715203788649585274557) * 10^40
        + 3967782764120876785027801572450357605764)),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP007Error2577 : ℝ := ((409050545734292758920081 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem nodeJet2N02705PlusPointP007BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP007Center2577‖ ≤ nodeJet2N02705PlusPointP007Error2577
          := by
  exact nodeExpN02705PlusPointP007BaseError2577

theorem nodeJet2N02705PlusPointP007DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP007Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP007Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP007Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP007Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP007Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP007Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP007BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP007Factor2577)

def nodeJet2N02705PlusPointP008Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((125937256369443206862002451 : ℚ) /
        23611832414348226068480000000))

def nodeJet2N02705PlusPointP008Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP008Factor2577 : RatPair2542 := (((((((((((1 * 10^40
        + 5213007558520101034361628888967023327728) * 10^40
        + 4087852455252795791420904461443644998987) * 10^40
        + 3867064510701144030592593023578858609181) * 10^40
        + 9371845062652653844090308062631941840419) * 10^40
        + 9475746337566938119600066732280563849073) * 10^40
        + 2381449649715171692628519196615202726066) * 10^40
        + 1694638977764530721173126915559763555458) * 10^40
        + 6408353441048442873085339989618019525375) : ℚ) /
        (((((((11825218843849928641990724182 * 10^40
        + 6943999297503659575328139769073080567729) * 10^40
        + 6273723891841736909889641918079042013623) * 10^40
        + 3014733967897595534920310941846977151147) * 10^40
        + 3990080606724338341689175105281638495792) * 10^40
        + 6435984785894492424799545669541853781057) * 10^40
        + 7607572679484829075704262940569259396357) * 10^40
        + 6729106410213355883014742571241728638976)),
    (((-((((34 * 10^40
        + 8726324192056853483063121766275103808624) * 10^40
        + 9102171519695638729278534913569026799503) * 10^40
        + 5428592061643706056503462146800088674584) * 10^40
        + 4400041923149741489374247972275957329537)) : ℚ) /
        (((10874382209509618225919740204836606 * 10^40
        + 3611089045377415057904678722670245730993) * 10^40
        + 5375498452436832589615588703700504124728) * 10^40
        + 4697252923626309130267766234698194354176)))

noncomputable def nodeJet2N02705PlusPointP008Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP008BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP008Center2577‖ ≤ nodeJet2N02705PlusPointP008Error2577
          := by
  exact nodeExpN02705PlusPointP008BaseError2577

theorem nodeJet2N02705PlusPointP008DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP008Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP008Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP008Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP008Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP008Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP008Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP008BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP008Factor2577)

def nodeJet2N02705PlusPointP009Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((187301696272790732683750413 : ℚ) /
        23611832414348226068480000000))

def nodeJet2N02705PlusPointP009Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP009Factor2577 : RatPair2542 := (((((((((((1 * 10^40
        + 5213007555656793442308216564458704233931) * 10^40
        + 8437495415049656568199353541925160553880) * 10^40
        + 2870459668014267447532790809317876336168) * 10^40
        + 8922535409697090403169665290681674962132) * 10^40
        + 7301427959960078826849765656927179163098) * 10^40
        + 264557395953965818616850532255568128422) * 10^40
        + 7162671881291619291819774292377082740995) * 10^40
        + 134801333529671585794471448543148725183) : ℚ) /
        (((((((11825218843849928641990724182 * 10^40
        + 6943999297503659575328139769073080567729) * 10^40
        + 6273723891841736909889641918079042013623) * 10^40
        + 3014733967897595534920310941846977151147) * 10^40
        + 3990080606724338341689175105281638495792) * 10^40
        + 6435984785894492424799545669541853781057) * 10^40
        + 7607572679484829075704262940569259396357) * 10^40
        + 6729106410213355883014742571241728638976)),
    (((-((((51 * 10^40
        + 8647411728080091317570445904291992176667) * 10^40
        + 5233981069441845963818633017421595335932) * 10^40
        + 2321018455584362450689913854343643157233) * 10^40
        + 6624267345511577795706524078351317412831)) : ℚ) /
        (((10874382209509618225919740204836606 * 10^40
        + 3611089045377415057904678722670245730993) * 10^40
        + 5375498452436832589615588703700504124728) * 10^40
        + 4697252923626309130267766234698194354176)))

noncomputable def nodeJet2N02705PlusPointP009Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP009BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP009Center2577‖ ≤ nodeJet2N02705PlusPointP009Error2577
          := by
  exact nodeExpN02705PlusPointP009BaseError2577

theorem nodeJet2N02705PlusPointP009DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP009Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP009Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP009Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP009Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP009Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP009Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP009BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP009Factor2577)

def nodeJet2N02705PlusPointP010Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((111420588356197715176385643 : ℚ) /
        11805916207174113034240000000))

def nodeJet2N02705PlusPointP010Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP010Factor2577 : RatPair2542 :=
    ((((((((((3803251888371371012788429227830838647797
    * 10^40
        + 7229711008937489325555688508250660279474) * 10^40
        + 4099366550073687368385497979846265278909) * 10^40
        + 4020020100616716261300869075727341874984) * 10^40
        + 464443676801442221582643866861570447215) * 10^40
        + 6961124167493240933269042618258520035308) * 10^40
        + 4284214294621666396088275944013114625533) * 10^40
        + 1316049581705816405399536055126256900655) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((30 * 10^40
        + 8528971782497680419690283944860653093564) * 10^40
        + 9497135122233746946810967015308644550332) * 10^40
        + 6916855736102298716657579943482891317866) * 10^40
        + 649669783374055762929661278611131376841)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705PlusPointP010Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP010BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP010Center2577‖ ≤ nodeJet2N02705PlusPointP010Error2577
          := by
  exact nodeExpN02705PlusPointP010BaseError2577

theorem nodeJet2N02705PlusPointP010DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP010Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP010Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP010Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP010Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP010Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP010Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP010BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP010Factor2577)

def nodeJet2N02705PlusPointP011Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((123268206202301004985337883 : ℚ) /
        11805916207174113034240000000))

def nodeJet2N02705PlusPointP011Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP011Factor2577 : RatPair2542 :=
    ((((((((((3803251887957181728772367247124496722712
    * 10^40
        + 4050703347430458718929595928759954248133) * 10^40
        + 4413354947995621628823964580726676817808) * 10^40
        + 3796935808957007698520343756164524295922) * 10^40
        + 5924098969239803855414188896487338421452) * 10^40
        + 8609076838909382788699080538276211535367) * 10^40
        + 9801795479910803021443373070389576737265) * 10^40
        + 2506272761580956438504720568105696334095) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((34 * 10^40
        + 1335595819022898928540692821262562250931) * 10^40
        + 3890060941623259848590203200276867320727) * 10^40
        + 7318237395431414952383573466460480167851) * 10^40
        + 3062818329971944951220897803363051333721)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705PlusPointP011Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP011BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP011Center2577‖ ≤ nodeJet2N02705PlusPointP011Error2577
          := by
  exact nodeExpN02705PlusPointP011BaseError2577

theorem nodeJet2N02705PlusPointP011DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP011Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP011Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP011Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP011Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP011Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP011Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP011BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP011Factor2577)

def nodeJet2N02705PlusPointP012Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((2710788774631016534924847 : ℚ) /
        236118324143482260684800000))

def nodeJet2N02705PlusPointP012Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP012Factor2577 : RatPair2542 :=
    ((((((((((950812971871023753174431386441339811893
    * 10^40
        + 2300764624308563130512460383140748814517) * 10^40
        + 3209152293965254306302356449614130594264) * 10^40
        + 1312134906098145257699734336954488255240) * 10^40
        + 7833415192614419560632917725577159016047) * 10^40
        + 3104071015437962583988346916329595731546) * 10^40
        + 23439495172638645880730745375934752202) * 10^40
        + 1396275820046483605630680942684127934359) : ℚ) /
        (((((((739076177740620540124420261 * 10^40
        + 4183999956093978723458008735567067535483) * 10^40
        + 1017107743240108556868102619879940125851) * 10^40
        + 4563420872993599720932519433865436071946) * 10^40
        + 7124380037920271146355573444080102405987) * 10^40
        + 402249049118405776549971604346365861316) * 10^40
        + 1100473292467801817231516433785578712272) * 10^40
        + 3545569150638334742688421410702608039936)),
    (((-((((18 * 10^40
        + 7657614650785145178564661833251732950591) * 10^40
        + 9305805999141818210180620806731125813271) * 10^40
        + 5435800070907690284098766370129615245998) * 10^40
        + 6627218951282581735193367004322674319725)) : ℚ) /
        (((2718595552377404556479935051209151 * 10^40
        + 5902772261344353764476169680667561432748) * 10^40
        + 3843874613109208147403897175925126031182) * 10^40
        + 1174313230906577282566941558674548588544)))

noncomputable def nodeJet2N02705PlusPointP012Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP012BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP012Center2577‖ ≤ nodeJet2N02705PlusPointP012Error2577
          := by
  exact nodeExpN02705PlusPointP012BaseError2577

theorem nodeJet2N02705PlusPointP012DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP012Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP012Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP012Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP012Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP012Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP012Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP012BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP012Factor2577)

def nodeJet2N02705PlusPointP013Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((29344407147130955527319553 : ℚ) /
        2361183241434822606848000000))

def nodeJet2N02705PlusPointP013Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP013Factor2577 : RatPair2542 :=
    ((((((((((3803251887013908954899222726486426443573
    * 10^40
        + 2004989647617675449753769417026305067207) * 10^40
        + 9009889470235419047238838803265276869025) * 10^40
        + 2612861278321954469088025303658612284620) * 10^40
        + 4718251247191380348552465599916742614188) * 10^40
        + 9034500813280854355971516051348896491629) * 10^40
        + 9560124591360419929553401236064806572610) * 10^40
        + 3805853947604314148951044739795202536911) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((40 * 10^40
        + 6280378619437070281999635067020638495156) * 10^40
        + 8858970303933860665987791698075667420099) * 10^40
        + 7478353084261890963598055427080709673966) * 10^40
        + 8352942693878672145186506673744590050055)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705PlusPointP013Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP013BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP013Center2577‖ ≤ nodeJet2N02705PlusPointP013Error2577
          := by
  exact nodeExpN02705PlusPointP013BaseError2577

theorem nodeJet2N02705PlusPointP013DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP013Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP013Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP013Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP013Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP013Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP013Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP013BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP013Factor2577)

def nodeJet2N02705PlusPointP014Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((167442242677902990093140313 : ℚ) /
        11805916207174113034240000000))

def nodeJet2N02705PlusPointP014Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP014Factor2577 : RatPair2542 :=
    ((((((((((3803251886044233598842397003648410931261
    * 10^40
        + 5246861054884604431198426906034641836036) * 10^40
        + 8185220125886698379242824140679883886272) * 10^40
        + 5495363090272780693771346204280055717569) * 10^40
        + 175670391144915444257418831569967499661) * 10^40
        + 6913458554252917207239097291940734915535) * 10^40
        + 9487943317852868375641665309739598388253) * 10^40
        + 586518504948990343952553688135062574775) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((46 * 10^40
        + 3655628897020224208482582320307804308071) * 10^40
        + 8879327856621846275331048455010497955693) * 10^40
        + 9672805524850404060284215974054161190912) * 10^40
        + 6096336370850429255366457154495198204131)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705PlusPointP014Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP014BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP014Center2577‖ ≤ nodeJet2N02705PlusPointP014Error2577
          := by
  exact nodeExpN02705PlusPointP014BaseError2577

theorem nodeJet2N02705PlusPointP014DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP014Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP014Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP014Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP014Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP014Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP014Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP014BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP014Factor2577)

def nodeJet2N02705PlusPointP015Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((182288341473529359843979701 : ℚ) /
        11805916207174113034240000000))

def nodeJet2N02705PlusPointP015Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP015Factor2577 : RatPair2542 :=
    ((((((((((3803251885270802863287693337244185110142
    * 10^40
        + 6934951506944192510268038739152225423449) * 10^40
        + 2221858169054587465855038507822713387883) * 10^40
        + 6851102110474434686626215699769027365168) * 10^40
        + 3910732665655253555773708774553441861194) * 10^40
        + 2321519760396344889365415007412143922122) * 10^40
        + 1798247718153783829165166234700838166063) * 10^40
        + 6959477075998952321423276805938227107567) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((50 * 10^40
        + 4765190998351523394906287864712189876087) * 10^40
        + 2590518151743497484471859622225312337630) * 10^40
        + 518797258565954147148288309748664289908) * 10^40
        + 5449279521737208601997701353925677275287)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705PlusPointP015Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP015BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP015Center2577‖ ≤ nodeJet2N02705PlusPointP015Error2577
          := by
  exact nodeExpN02705PlusPointP015BaseError2577

theorem nodeJet2N02705PlusPointP015DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP015Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP015Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP015Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP015Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP015Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP015Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP015BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP015Factor2577)

def nodeJet2N02705PlusPointP016Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((96508645919919764395179147 : ℚ) /
        5902958103587056517120000000))

def nodeJet2N02705PlusPointP016Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP016Factor2577 : RatPair2542 :=
    ((((((((((950812971167746805564661731817555110943
    * 10^40
        + 6592609180349366808074354943150156520025) * 10^40
        + 892922971192712273403039610488447910207) * 10^40
        + 7517917916290738005361259279007498808888) * 10^40
        + 7799646065599414042700108376525496894) * 10^40
        + 1500034708850531600236188304692921735630) * 10^40
        + 4803187811105917109787479850512430290092) * 10^40
        + 2139818181537904454054674988522451511663) : ℚ) /
        (((((((739076177740620540124420261 * 10^40
        + 4183999956093978723458008735567067535483) * 10^40
        + 1017107743240108556868102619879940125851) * 10^40
        + 4563420872993599720932519433865436071946) * 10^40
        + 7124380037920271146355573444080102405987) * 10^40
        + 402249049118405776549971604346365861316) * 10^40
        + 1100473292467801817231516433785578712272) * 10^40
        + 3545569150638334742688421410702608039936)),
    (((-((((26 * 10^40
        + 7237085471176526450927720660298641282937) * 10^40
        + 4023659077945796143360972881277761631868) * 10^40
        + 4031238309395980039350763010094893730223) * 10^40
        + 3350071204440659248580390559070228686889)) : ℚ) /
        (((2718595552377404556479935051209151 * 10^40
        + 5902772261344353764476169680667561432748) * 10^40
        + 3843874613109208147403897175925126031182) * 10^40
        + 1174313230906577282566941558674548588544)))

noncomputable def nodeJet2N02705PlusPointP016Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP016BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP016Center2577‖ ≤ nodeJet2N02705PlusPointP016Error2577
          := by
  exact nodeExpN02705PlusPointP016BaseError2577

theorem nodeJet2N02705PlusPointP016DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP016Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP016Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP016Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP016Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP016Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP016Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP016BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP016Factor2577)

def nodeJet2N02705PlusPointP017Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((213857607167923887040711041 : ℚ) /
        11805916207174113034240000000))

def nodeJet2N02705PlusPointP017Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP017Factor2577 : RatPair2542 :=
    ((((((((((3803251883407878741794776942428189007893
    * 10^40
        + 6751415930844002101604669226897562782549) * 10^40
        + 5054566967440024865203010959977007870937) * 10^40
        + 1031729169855002145053397705998858742969) * 10^40
        + 4111044866948913753434947417469928342412) * 10^40
        + 5383783673979025409159548950575703113818) * 10^40
        + 3571060506224960726312120905993173012723) * 10^40
        + 2719729741874893102042417851138190526247) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((59 * 10^40
        + 2182007121080573716785193255230266348819) * 10^40
        + 3157365498522604522664540004149116491410) * 10^40
        + 9402950576840767327672232425909111207421) * 10^40
        + 5936557897357583006864796525014059843867)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705PlusPointP017Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP017BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP017Center2577‖ ≤ nodeJet2N02705PlusPointP017Error2577
          := by
  exact nodeExpN02705PlusPointP017BaseError2577

theorem nodeJet2N02705PlusPointP017DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP017Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP017Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP017Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP017Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP017Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP017Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP017BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP017Factor2577)

def nodeJet2N02705PlusPointP018Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((55434221733839136935063079 : ℚ) /
        2951479051793528258560000000))

def nodeJet2N02705PlusPointP018Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP018Factor2577 : RatPair2542 :=
    ((((((((((237703242681038483439305382431092231425
    * 10^40
        + 1298466430633887445573186416444984398209) * 10^40
        + 748905802037383213125968139989534428336) * 10^40
        + 1996254082341726412647306602953173948935) * 10^40
        + 9492882950487235253548376382962178938763) * 10^40
        + 7478442219150494017490928677578556305980) * 10^40
        + 4807395710856724884931700252443894193729) * 10^40
        + 9861393260625629644240472428957005514167) : ℚ) /
        (((((((184769044435155135031105065 * 10^40
        + 3545999989023494680864502183891766883870) * 10^40
        + 7754276935810027139217025654969985031462) * 10^40
        + 8640855218248399930233129858466359017986) * 10^40
        + 6781095009480067786588893361020025601496) * 10^40
        + 7600562262279601444137492901086591465329) * 10^40
        + 275118323116950454307879108446394678068) * 10^40
        + 886392287659583685672105352675652009984)),
    (((-((((15 * 10^40
        + 3500028005847675705219417115251375173794) * 10^40
        + 6196015733765826340584365633344994185560) * 10^40
        + 8366498876065926641467319526215236219420) * 10^40
        + 9065046886340196712210938603379930460573)) : ℚ) /
        (((1359297776188702278239967525604575 * 10^40
        + 7951386130672176882238084840333780716374) * 10^40
        + 1921937306554604073701948587962563015591) * 10^40
        + 587156615453288641283470779337274294272)))

noncomputable def nodeJet2N02705PlusPointP018Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP018BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP018Center2577‖ ≤ nodeJet2N02705PlusPointP018Error2577
          := by
  exact nodeExpN02705PlusPointP018BaseError2577

theorem nodeJet2N02705PlusPointP018DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP018Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP018Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP018Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP018Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP018Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP018Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP018BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP018Factor2577)

def nodeJet2N02705PlusPointP019Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((11798844492939419238077853 : ℚ) /
        590295810358705651712000000))

def nodeJet2N02705PlusPointP019Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP019Factor2577 : RatPair2542 :=
    ((((((((((237703242620356530776419417176714968575
    * 10^40
        + 2970112751284208788067130825726911816867) * 10^40
        + 9903262529209165237181941336113715511290) * 10^40
        + 1206241138382948194209815813643993620453) * 10^40
        + 5522638909672894521307514790160789813482) * 10^40
        + 467903103841751398823166698377102512266) * 10^40
        + 6304095540908488865488303417323449268100) * 10^40
        + 4702257400468007997646226527040628094471) : ℚ) /
        (((((((184769044435155135031105065 * 10^40
        + 3545999989023494680864502183891766883870) * 10^40
        + 7754276935810027139217025654969985031462) * 10^40
        + 8640855218248399930233129858466359017986) * 10^40
        + 6781095009480067786588893361020025601496) * 10^40
        + 7600562262279601444137492901086591465329) * 10^40
        + 275118323116950454307879108446394678068) * 10^40
        + 886392287659583685672105352675652009984)),
    (((-((((16 * 10^40
        + 3357841370871524198441667724661897001680) * 10^40
        + 1715387956961012547019313647203625791735) * 10^40
        + 6237571101873011743819057736015794203180) * 10^40
        + 438231264563888313893452643358043860555)) : ℚ) /
        (((1359297776188702278239967525604575 * 10^40
        + 7951386130672176882238084840333780716374) * 10^40
        + 1921937306554604073701948587962563015591) * 10^40
        + 587156615453288641283470779337274294272)))

noncomputable def nodeJet2N02705PlusPointP019Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP019BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP019Center2577‖ ≤ nodeJet2N02705PlusPointP019Error2577
          := by
  exact nodeExpN02705PlusPointP019BaseError2577

theorem nodeJet2N02705PlusPointP019DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP019Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP019Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP019Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP019Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP019Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP019Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP019BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP019Factor2577)

def nodeJet2N02705PlusPointP020Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((251461754510132159483335377 : ℚ) /
        11805916207174113034240000000))

def nodeJet2N02705PlusPointP020Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP020Factor2577 : RatPair2542 :=
    ((((((((((3803251880801351091228584930696444606119
    * 10^40
        + 4951252604973931176610564191042128863431) * 10^40
        + 2612520660132509361594345870590385157662) * 10^40
        + 7833883368565139274699520837876505373611) * 10^40
        + 6831850903935235026475008030091336065193) * 10^40
        + 9410255057858540126544867332382198679788) * 10^40
        + 9999654464808669118421318294211590401187) * 10^40
        + 8132295575374652494700759898077500185735) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((69 * 10^40
        + 6309700982820152704745508703143118353744) * 10^40
        + 2300953744514748790213007499605039044162) * 10^40
        + 248485959416114839988843158221408971411) * 10^40
        + 8327047799162164397109420220400060277899)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705PlusPointP020Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP020BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP020Center2577‖ ≤ nodeJet2N02705PlusPointP020Error2577
          := by
  exact nodeExpN02705PlusPointP020BaseError2577

theorem nodeJet2N02705PlusPointP020DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP020Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP020Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP020Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP020Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP020Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP020Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP020BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP020Factor2577)

def nodeJet2N02705PlusPointP021Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((264384479371882101864279921 : ℚ) /
        11805916207174113034240000000))

def nodeJet2N02705PlusPointP021Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP021Factor2577 : RatPair2542 :=
    ((((((((((3803251879808349763840658932618949372739
    * 10^40
        + 5602379052117142867422396766196427004984) * 10^40
        + 9606149655181196659506657959128914402910) * 10^40
        + 702350713149969692507165645436301090954) * 10^40
        + 5731589764576521152762499607058467542995) * 10^40
        + 1445890970892381130227605990591708673956) * 10^40
        + 4668352076895569395123060711993887929029) * 10^40
        + 2547597133397459262895413793392176737607) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((5 * 10^40
        + 6314872930007800148999514286329667530144) * 10^40
        + 7472127913013358960364511574791556144600) * 10^40
        + 1636680018826013998175730186226063736212) * 10^40
        + 4994752342227466389817315258185403713879)) : ℚ) /
        (((418245469596523777919990007878331 * 10^40
        + 138888040206823656073256873948855605038) * 10^40
        + 2129826863555262791908291873219250158643) * 10^40
        + 4026817420139473428087221778257622859776)))

noncomputable def nodeJet2N02705PlusPointP021Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP021BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP021Center2577‖ ≤ nodeJet2N02705PlusPointP021Error2577
          := by
  exact nodeExpN02705PlusPointP021BaseError2577

theorem nodeJet2N02705PlusPointP021DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP021Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP021Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP021Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP021Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP021Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP021Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP021BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP021Factor2577)

def nodeJet2N02705PlusPointP022Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((54199761301639112700100539 : ℚ) /
        2361183241434822606848000000))

def nodeJet2N02705PlusPointP022Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP022Factor2577 : RatPair2542 :=
    ((((((((((3803251879280845533742675695876589671278
    * 10^40
        + 5395179128325403529600165863444405756549) * 10^40
        + 2745989061922908007677250365463092292526) * 10^40
        + 4265185014282134483364877139013000303577) * 10^40
        + 9240284557328867205634199809350113861003) * 10^40
        + 7949905235968238831754919353633156595147) * 10^40
        + 1134240472802700363939353223839479847308) * 10^40
        + 5844792290315424676158440811635690198711) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((75 * 10^40
        + 408738275225578065635680531751509478612) * 10^40
        + 9476586807182297361011710095016136838536) * 10^40
        + 9568023161248477583284188684720825949350) * 10^40
        + 9859511073160994234394392894764526087965)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705PlusPointP022Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP022BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP022Center2577‖ ≤ nodeJet2N02705PlusPointP022Error2577
          := by
  exact nodeExpN02705PlusPointP022BaseError2577

theorem nodeJet2N02705PlusPointP022DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP022Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP022Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP022Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP022Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP022Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP022Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP022BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP022Factor2577)

def nodeJet2N02705PlusPointP023Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((145034570365256380837972839 : ℚ) /
        5902958103587056517120000000))

def nodeJet2N02705PlusPointP023Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP023Factor2577 : RatPair2542 :=
    ((((((((((950812969421747246906033392478667054234
    * 10^40
        + 5030617047374508050616125468753261240308) * 10^40
        + 9495418311368036595260719098325482472458) * 10^40
        + 4222195831287868155650107855455305118374) * 10^40
        + 3255187442542863395681456851465964349437) * 10^40
        + 7798154422605261702915358514345386425503) * 10^40
        + 9598448648561542872099303232002199488981) * 10^40
        + 8007114702484858700662635293598230087735) : ℚ) /
        (((((((739076177740620540124420261 * 10^40
        + 4183999956093978723458008735567067535483) * 10^40
        + 1017107743240108556868102619879940125851) * 10^40
        + 4563420872993599720932519433865436071946) * 10^40
        + 7124380037920271146355573444080102405987) * 10^40
        + 402249049118405776549971604346365861316) * 10^40
        + 1100473292467801817231516433785578712272) * 10^40
        + 3545569150638334742688421410702608039936)),
    (((-((((40 * 10^40
        + 1607705791833669216698949004314918588866) * 10^40
        + 2976795429216599380340295291863511016620) * 10^40
        + 9870747728524181457081603798028527866278) * 10^40
        + 3009251047320046010741973887359023097693)) : ℚ) /
        (((2718595552377404556479935051209151 * 10^40
        + 5902772261344353764476169680667561432748) * 10^40
        + 3843874613109208147403897175925126031182) * 10^40
        + 1174313230906577282566941558674548588544)))

noncomputable def nodeJet2N02705PlusPointP023Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP023BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP023Center2577‖ ≤ nodeJet2N02705PlusPointP023Error2577
          := by
  exact nodeExpN02705PlusPointP023BaseError2577

theorem nodeJet2N02705PlusPointP023DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP023Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP023Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP023Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP023Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP023Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP023Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP023BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP023Factor2577)

def nodeJet2N02705PlusPointP024Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((149416547034989152754795001 : ℚ) /
        5902958103587056517120000000))

def nodeJet2N02705PlusPointP024Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP024Factor2577 : RatPair2542 :=
    ((((((((((950812969229544878582780444456965938400
    * 10^40
        + 2922026319244796177194946889815892356159) * 10^40
        + 2648645971378381723679156338469928786095) * 10^40
        + 6162508957110122036084614932292199676048) * 10^40
        + 3927052419300228743584939803183794054694) * 10^40
        + 7042957121831652881729238129393158206734) * 10^40
        + 2140183252441990508164544111777744274923) * 10^40
        + 2429334189797900266176352559236043556215) : ℚ) /
        (((((((739076177740620540124420261 * 10^40
        + 4183999956093978723458008735567067535483) * 10^40
        + 1017107743240108556868102619879940125851) * 10^40
        + 4563420872993599720932519433865436071946) * 10^40
        + 7124380037920271146355573444080102405987) * 10^40
        + 402249049118405776549971604346365861316) * 10^40
        + 1100473292467801817231516433785578712272) * 10^40
        + 3545569150638334742688421410702608039936)),
    (((-((((41 * 10^40
        + 3741610092944309163863866908696901645790) * 10^40
        + 7176294538333098169010145194351385026880) * 10^40
        + 8345527779863502826465978117236167681598) * 10^40
        + 6098393926440786909975722016015357096387)) : ℚ) /
        (((2718595552377404556479935051209151 * 10^40
        + 5902772261344353764476169680667561432748) * 10^40
        + 3843874613109208147403897175925126031182) * 10^40
        + 1174313230906577282566941558674548588544)))

noncomputable def nodeJet2N02705PlusPointP024Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP024BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP024Center2577‖ ≤ nodeJet2N02705PlusPointP024Error2577
          := by
  exact nodeExpN02705PlusPointP024BaseError2577

theorem nodeJet2N02705PlusPointP024DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP024Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP024Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP024Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP024Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP024Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP024Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP024BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP024Factor2577)

def nodeJet2N02705PlusPointP025Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((4840960678205345786172339 : ℚ) /
        184467440737095516160000000))

def nodeJet2N02705PlusPointP025Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP025Factor2577 : RatPair2542 :=
    ((((((((((928528290019995566402499282171496937 *
    10^40
        + 9979714627292020043159197212480560060961) * 10^40
        + 3302284508950805102412657113852095120619) * 10^40
        + 6141305599141730807339321915772113176572) * 10^40
        + 1693546867120288697498898263801030110714) * 10^40
        + 9015401380939672454379167431692261568267) * 10^40
        + 1616485450234751658070726105132598615976) * 10^40
        + 798536127134692599099130616182185935167) : ℚ) /
        (((((((721754079824824746215254 * 10^40
        + 1615414062457123026097126961655827214390) * 10^40
        + 1202165144280507918512566506464726504029) * 10^40
        + 1518128340696282812227473163509634214914) * 10^40
        + 104613652380781514791362864691484475005) * 10^40
        + 8467189696337029693141162081644869497911) * 10^40
        + 4415137180949675587712140152767368729211) * 10^40
        + 2034712469873670248772156661533889265664)),
    (((-((((1 * 10^40
        + 3404853111270781601833180013586369054338) * 10^40
        + 2119288738849316460720641062381015692018) * 10^40
        + 2459378483251356275658064163286926216456) * 10^40
        + 4837576410815138474339070632364960804193)) : ℚ) /
        (((84956111011793892389997970350285 * 10^40
        + 9871961633167011055139880302520861294773) * 10^40
        + 3870121081659662754606371786747660188474) * 10^40
        + 4411697288465830540080216923708579643392)))

noncomputable def nodeJet2N02705PlusPointP025Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP025BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP025Center2577‖ ≤ nodeJet2N02705PlusPointP025Error2577
          := by
  exact nodeExpN02705PlusPointP025BaseError2577

theorem nodeJet2N02705PlusPointP025DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP025Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP025Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP025Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP025Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP025Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP025Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP025BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP025Factor2577)

def nodeJet2N02705PlusPointP026Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((10032849088039534343392071 : ℚ) /
        368934881474191032320000000))

def nodeJet2N02705PlusPointP026Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP026Factor2577 : RatPair2542 :=
    ((((((((((3714113159049394741483802633558256884 *
    10^40
        + 7156838703880969192801171928164166144375) * 10^40
        + 1731941133426157137764983573942991954091) * 10^40
        + 4053865050759447821750438576508478097988) * 10^40
        + 2383249136157041036178566265041656883788) * 10^40
        + 7620068474861438118127066393096689514607) * 10^40
        + 1566497214527212641562105894410473277325) * 10^40
        + 3260476074728415913357782422093794310135) : ℚ) /
        (((((((2887016319299298984861016 * 10^40
        + 6461656249828492104388507846623308857560) * 10^40
        + 4808660577122031674050266025858906016116) * 10^40
        + 6072513362785131248909892654038536859656) * 10^40
        + 418454609523126059165451458765937900023) * 10^40
        + 3868758785348118772564648326579477991645) * 10^40
        + 7660548723798702350848560611069474916844) * 10^40
        + 8138849879494680995088626646135557062656)),
    (((-((((2 * 10^40
        + 7781442001420068905636668866716001138093) * 10^40
        + 2585466621853596648956488621562240124130) * 10^40
        + 7786824301292545576021781393096694819607) * 10^40
        + 8729494108670899841161900589039901332477)) : ℚ) /
        (((169912222023587784779995940700571 * 10^40
        + 9743923266334022110279760605041722589546) * 10^40
        + 7740242163319325509212743573495320376948) * 10^40
        + 8823394576931661080160433847417159286784)))

noncomputable def nodeJet2N02705PlusPointP026Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP026BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP026Center2577‖ ≤ nodeJet2N02705PlusPointP026Error2577
          := by
  exact nodeExpN02705PlusPointP026BaseError2577

theorem nodeJet2N02705PlusPointP026DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP026Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP026Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP026Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP026Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP026Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP026Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP026BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP026Factor2577)

def nodeJet2N02705PlusPointP027Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((21078498488072348391776841 : ℚ) /
        737869762948382064640000000))

def nodeJet2N02705PlusPointP027Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP027Factor2577 : RatPair2542 :=
    ((((((((((14856452629990205425338777083316036044 *
    10^40
        + 6701162738469201706718049118856882552892) * 10^40
        + 6264085165807585339866336526489415683784) * 10^40
        + 1462271591503397129859808178868379602633) * 10^40
        + 1913446248223164416790700719503601029248) * 10^40
        + 1184163454540471822964684494377133008179) * 10^40
        + 4919082879881503577415324610427345634756) * 10^40
        + 8457098951237170570814526731841203972567) : ℚ) /
        (((((((11548065277197195939444066 * 10^40
        + 5846624999313968417554031386493235430241) * 10^40
        + 9234642308488126696201064103435624064466) * 10^40
        + 4290053451140524995639570616154147438624) * 10^40
        + 1673818438092504236661805835063751600093) * 10^40
        + 5475035141392475090258593306317911966583) * 10^40
        + 642194895194809403394242444277899667379) * 10^40
        + 2555399517978723980354506584542228250624)),
    (((-((((5 * 10^40
        + 8367376812385582950828434726660685093002) * 10^40
        + 3927310364989410313860090305154164475182) * 10^40
        + 3277356360524972714035150560638560331765) * 10^40
        + 1737726628543545936662018997341082108467)) : ℚ) /
        (((339824444047175569559991881401143 * 10^40
        + 9487846532668044220559521210083445179093) * 10^40
        + 5480484326638651018425487146990640753897) * 10^40
        + 7646789153863322160320867694834318573568)))

noncomputable def nodeJet2N02705PlusPointP027Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP027BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP027Center2577‖ ≤ nodeJet2N02705PlusPointP027Error2577
          := by
  exact nodeExpN02705PlusPointP027BaseError2577

theorem nodeJet2N02705PlusPointP027DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP027Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP027Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP027Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP027Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP027Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP027Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP027BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP027Factor2577)

def nodeJet2N02705PlusPointP028Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((85917920262979814161755141 : ℚ) /
        2951479051793528258560000000))

def nodeJet2N02705PlusPointP028Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP028Factor2577 : RatPair2542 :=
    ((((((((((237703242039170787415443190508324017484
    * 10^40
        + 4273626975312468504038753140970033810510) * 10^40
        + 3562203945929364106246030270787638157606) * 10^40
        + 3331670446214788931863237683520734731860) * 10^40
        + 8189471306021751640943015440953814430056) * 10^40
        + 6566795074945928285348320406210052133703) * 10^40
        + 8019570670699176739874491397924214583044) * 10^40
        + 3059127232903569849423653955233327341007) : ℚ) /
        (((((((184769044435155135031105065 * 10^40
        + 3545999989023494680864502183891766883870) * 10^40
        + 7754276935810027139217025654969985031462) * 10^40
        + 8640855218248399930233129858466359017986) * 10^40
        + 6781095009480067786588893361020025601496) * 10^40
        + 7600562262279601444137492901086591465329) * 10^40
        + 275118323116950454307879108446394678068) * 10^40
        + 886392287659583685672105352675652009984)),
    (((-((((23 * 10^40
        + 7910856400115940009082244989490256290419) * 10^40
        + 3415207812350306598528423136907480818728) * 10^40
        + 8918377896097655333173454542104753915794) * 10^40
        + 9396084254168825953911073919904511010567)) : ℚ) /
        (((1359297776188702278239967525604575 * 10^40
        + 7951386130672176882238084840333780716374) * 10^40
        + 1921937306554604073701948587962563015591) * 10^40
        + 587156615453288641283470779337274294272)))

noncomputable def nodeJet2N02705PlusPointP028Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP028BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP028Center2577‖ ≤ nodeJet2N02705PlusPointP028Error2577
          := by
  exact nodeExpN02705PlusPointP028BaseError2577

theorem nodeJet2N02705PlusPointP028DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP028Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP028Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP028Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP028Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP028Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP028Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP028BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP028Factor2577)

def nodeJet2N02705PlusPointP029Input2577 : RatPair2542 := ((((-((9253 * 10^40
        + 2310500310605818658216670868978403073565) * 10^40
        + 4438856658060667417950293650796076562987)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((88359795091650310792539297 : ℚ) /
        2951479051793528258560000000))

def nodeJet2N02705PlusPointP029Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705PlusPointP029Factor2577 : RatPair2542 :=
    ((((((((((237703241975777872307224103501896426808
    * 10^40
        + 8889128773156326366407504217629335403539) * 10^40
        + 6161455273754567542493929874148847159968) * 10^40
        + 912731674442921356752327789802381973145) * 10^40
        + 6897289420651211521804171295690762954703) * 10^40
        + 6792376352285255856265900896347283123064) * 10^40
        + 1483355764082081188133027931772497080597) * 10^40
        + 3368676708214940363677850639701757228775) : ℚ) /
        (((((((184769044435155135031105065 * 10^40
        + 3545999989023494680864502183891766883870) * 10^40
        + 7754276935810027139217025654969985031462) * 10^40
        + 8640855218248399930233129858466359017986) * 10^40
        + 6781095009480067786588893361020025601496) * 10^40
        + 7600562262279601444137492901086591465329) * 10^40
        + 275118323116950454307879108446394678068) * 10^40
        + 886392287659583685672105352675652009984)),
    (((-((((24 * 10^40
        + 4672525327072060455186527641642674215106) * 10^40
        + 5597425351270810183277166329797995930449) * 10^40
        + 2508669178822572769639930759381707655056) * 10^40
        + 5884650390256222018437803519839131714939)) : ℚ) /
        (((1359297776188702278239967525604575 * 10^40
        + 7951386130672176882238084840333780716374) * 10^40
        + 1921937306554604073701948587962563015591) * 10^40
        + 587156615453288641283470779337274294272)))

noncomputable def nodeJet2N02705PlusPointP029Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705PlusPointP029BaseError2577 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP029Center2577‖ ≤ nodeJet2N02705PlusPointP029Error2577
          := by
  exact nodeExpN02705PlusPointP029BaseError2577

theorem nodeJet2N02705PlusPointP029DerivativeError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP029Factor2577 * embedPair2542
          nodeJet2N02705PlusPointP029Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705PlusPointP029Factor2577 : ℝ) *
            nodeJet2N02705PlusPointP029Error2577 := by
  have hx : |nodeJet2N02705PlusPointPosition2577| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705PlusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) nodeJet2N02705PlusPointPosition2577 = embedPair2542
          nodeJet2N02705PlusPointP029Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705PlusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705PlusPointP029Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705PlusPointP029BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705PlusPointP029Factor2577)

theorem nodeJet2N02705PlusPointGrid2577 :
    -stripRadius2303 + (2705 : ℝ) * (2 * stripRadius2303 / 10240) =
      nodeJet2N02705PlusPointPosition2577 := by
  norm_num [stripRadius2303, nodeJet2N02705PlusPointPosition2577]

end ConnesWeilRH.Dev
