import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

def compactInputP0002542 : RatPair2542 :=
  ((((-((263275 * 10^40
        + 1125171558294111539978267023056917167198) * 10^40
        + 1332055800215011207425642192228936552933)) : ℚ) /
        ((561665 * 10^40
        + 4151492452771926362187803248812537956572) * 10^40
        + 1774117228738064370319589815091200000000)),
    (((-362039942185747774262029) : ℚ) /
        461168601842738790400000000))

def compactOutputP0002542 : RatState2542 :=
  ((((1852300462860835 : ℚ) /
        19807040628566084398385987584),
    (((-1490300349709075) : ℚ) /
        316912650057057350374175801344)),
    ((16211342998361 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0002542 : compactExp2542 compactInputP0002542 6 = compactOutputP0002542 := by
  cbv

theorem compactErrorP0002542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0002541) - nodeSP0002541 6‖ ≤
      nodeEP0002541 6 := by
  have hz : ‖embedPair2542 compactInputP0002542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0002542]
  have h := compactExp_error2542 compactInputP0002542 hz 6
  rw [compactReplayP0002542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0002542, compactOutputP0002542,
    nodeZP0002541, nodeSP0002541, nodeEP0002541]

def compactInputP0012542 : RatPair2542 :=
  ((((-((337 * 10^40
        + 2581669391407268959104378187086677265835) * 10^40
        + 8255161039993466428760315913304611097119)) : ℚ) /
        ((719 * 10^40
        + 4993359455299629143016013800955751656510) * 10^40
        + 7876832460263855226589589543321600000000)),
    (((-362039942185747774262029) : ℚ) /
        461168601842738790400000000))

def compactOutputP0012542 : RatState2542 :=
  ((((1852306412185369 : ℚ) /
        19807040628566084398385987584),
    (((-5961220545363791) : ℚ) /
        1267650600228229401496703205376)),
    ((4052846825179 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)))

theorem compactReplayP0012542 : compactExp2542 compactInputP0012542 6 = compactOutputP0012542 := by
  cbv

theorem compactErrorP0012542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0012541) - nodeSP0012541 6‖ ≤
      nodeEP0012541 6 := by
  have hz : ‖embedPair2542 compactInputP0012542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0012542]
  have h := compactExp_error2542 compactInputP0012542 hz 6
  rw [compactReplayP0012542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0012542, compactOutputP0012542,
    nodeZP0012541, nodeSP0012541, nodeEP0012541]

def compactInputP0022542 : RatPair2542 :=
  ((((-((8811 * 10^40
        + 7974475504972435624923961780003357186703) * 10^40
        + 8778883137590559728133612891529783413279)) : ℚ) /
        ((18798 * 10^40
        + 9006191557813387101993297027860527661132) * 10^40
        + 3254270395238148625433432693145600000000)),
    ((362039942185747774262029 : ℚ) /
        461168601842738790400000000))

def compactOutputP0022542 : RatState2542 :=
  ((((29636951857208525 : ℚ) /
        316912650057057350374175801344),
    ((5961230454060959 : ℚ) /
        1267650600228229401496703205376)),
    ((8105705114019 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

theorem compactReplayP0022542 : compactExp2542 compactInputP0022542 6 = compactOutputP0022542 := by
  cbv

theorem compactErrorP0022542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0022541) - nodeSP0022541 6‖ ≤
      nodeEP0022541 6 := by
  have hz : ‖embedPair2542 compactInputP0022542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0022542]
  have h := compactExp_error2542 compactInputP0022542 hz 6
  rw [compactReplayP0022542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0022542, compactOutputP0022542,
    nodeZP0022541, nodeSP0022541, nodeEP0022541]

def compactInputP0032542 : RatPair2542 :=
  ((((-((1163809 * 10^40
        + 2803467370453462244264746520956969698628) * 10^40
        + 520753972540498124346843478850030302933)) : ℚ) /
        ((2482845 * 10^40
        + 9583712326578763211258577850560960882752) * 10^40
        + 4361609409025312370319589815091200000000)),
    ((362039942185747774262029 : ℚ) /
        461168601842738790400000000))

def compactOutputP0032542 : RatState2542 :=
  ((((118547917597779263 : ℚ) /
        1267650600228229401496703205376),
    ((2980617996978255 : ℚ) /
        633825300114114700748351602688)),
    ((16211423046571 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0032542 : compactExp2542 compactInputP0032542 6 = compactOutputP0032542 := by
  cbv

theorem compactErrorP0032542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0032541) - nodeSP0032541 6‖ ≤
      nodeEP0032541 6 := by
  have hz : ‖embedPair2542 compactInputP0032542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0032542]
  have h := compactExp_error2542 compactInputP0032542 hz 6
  rw [compactReplayP0032542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0032542, compactOutputP0032542,
    nodeZP0032541, nodeSP0032541, nodeEP0032541]

def compactInputP0042542 : RatPair2542 :=
  ((((-((20219 * 10^40
        + 5286412261941775910972762094659285731921) * 10^40
        + 6451931165132029084895488306568845913279)) : ℚ) /
        ((43135 * 10^40
        + 9130219364496567868722082594457765491888) * 10^40
        + 9118561522531428625433432693145600000000)),
    (((-362039942185747774262029) : ℚ) /
        461168601842738790400000000))

def compactOutputP0042542 : RatState2542 :=
  ((((118547983063412177 : ℚ) /
        1267650600228229401496703205376),
    (((-5961239285925659) : ℚ) /
        1267650600228229401496703205376)),
    ((16211430663721 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0042542 : compactExp2542 compactInputP0042542 6 = compactOutputP0042542 := by
  cbv

theorem compactErrorP0042542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0042541) - nodeSP0042541 6‖ ≤
      nodeEP0042541 6 := by
  have hz : ‖embedPair2542 compactInputP0042542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0042542]
  have h := compactExp_error2542 compactInputP0042542 hz 6
  rw [compactReplayP0042542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0042542, compactOutputP0042542,
    nodeZP0042541, nodeSP0042541, nodeEP0042541]

def compactInputP0052542 : RatPair2542 :=
  ((((-((960037 * 10^40
        + 6342012607625608885787797769382884372499) * 10^40
        + 345329265333619955745170436550090908799)) : ℚ) /
        ((2048123 * 10^40
        + 5583500882725006604582039066398344845805) * 10^40
        + 6680083775291233110958769445273600000000)),
    ((0 : ℚ) /
        1))

def compactOutputP0052542 : RatState2542 :=
  ((((29674293423158639 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1)),
    ((15546262950713 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0052542 : compactExp2542 compactInputP0052542 6 = compactOutputP0052542 := by
  cbv

theorem compactErrorP0052542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0052541) - nodeSP0052541 6‖ ≤
      nodeEP0052541 6 := by
  have hz : ‖embedPair2542 compactInputP0052542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0052542]
  have h := compactExp_error2542 compactInputP0052542 hz 6
  rw [compactReplayP0052542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0052542, compactOutputP0052542,
    nodeZP0052541, nodeSP0052541, nodeEP0052541]

def compactInputP0062542 : RatPair2542 :=
  ((((-42948756700390030649865186028202667) : ℚ) /
        91625959598833823313644748800000000),
    ((0 : ℚ) /
        1))

def compactOutputP0062542 : RatState2542 :=
  ((((1854649085141411 : ℚ) /
        19807040628566084398385987584),
    ((0 : ℚ) /
        1)),
    ((15546303657975 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0062542 : compactExp2542 compactInputP0062542 6 = compactOutputP0062542 := by
  cbv

theorem compactErrorP0062542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0062541) - nodeSP0062541 6‖ ≤
      nodeEP0062541 6 := by
  have hz : ‖embedPair2542 compactInputP0062542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0062542]
  have h := compactExp_error2542 compactInputP0062542 hz 6
  rw [compactReplayP0062542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0062542, compactOutputP0062542,
    nodeZP0062541, nodeSP0062541, nodeEP0062541]

def compactInputP0072542 : RatPair2542 :=
  ((((-((1163809 * 10^40
        + 2803467370453462244264746520956969698628) * 10^40
        + 520753972540498124346843478850030302933)) : ℚ) /
        ((2482845 * 10^40
        + 9583712326578763211258577850560960882752) * 10^40
        + 4361609409025312370319589815091200000000)),
    ((0 : ℚ) /
        1))

def compactOutputP0072542 : RatState2542 :=
  ((((59348852350625755 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1)),
    ((15546321728495 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0072542 : compactExp2542 compactInputP0072542 6 = compactOutputP0072542 := by
  cbv

theorem compactErrorP0072542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0072541) - nodeSP0072541 6‖ ≤
      nodeEP0072541 6 := by
  have hz : ‖embedPair2542 compactInputP0072542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0072542]
  have h := compactExp_error2542 compactInputP0072542 hz 6
  rw [compactReplayP0072542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0072542, compactOutputP0072542,
    nodeZP0072541, nodeSP0072541, nodeEP0072541]

def compactInputP0082542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-260739661220379310273297) : ℚ) /
        922337203685477580800000000))

def compactOutputP0082542 : RatState2542 :=
  ((((118677871587465679 : ℚ) /
        1267650600228229401496703205376),
    (((-2147407588285621) : ℚ) /
        1267650600228229401496703205376)),
    ((15784642939527 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0082542 : compactExp2542 compactInputP0082542 6 = compactOutputP0082542 := by
  cbv

theorem compactErrorP0082542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0082541) - nodeSP0082541 6‖ ≤
      nodeEP0082541 6 := by
  have hz : ‖embedPair2542 compactInputP0082542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0082542]
  have h := compactExp_error2542 compactInputP0082542 hz 6
  rw [compactReplayP0082542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0082542, compactOutputP0082542,
    nodeZP0082541, nodeSP0082541, nodeEP0082541]

def compactInputP0092542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-387788191040974601829711) : ℚ) /
        922337203685477580800000000))

def compactOutputP0092542 : RatState2542 :=
  ((((118654329142908059 : ℚ) /
        1267650600228229401496703205376),
    (((-3193546543837981) : ℚ) /
        1267650600228229401496703205376)),
    ((1987657251143 : ℚ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472)))

theorem compactReplayP0092542 : compactExp2542 compactInputP0092542 6 = compactOutputP0092542 := by
  cbv

theorem compactErrorP0092542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0092541) - nodeSP0092541 6‖ ≤
      nodeEP0092541 6 := by
  have hz : ‖embedPair2542 compactInputP0092542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0092542]
  have h := compactExp_error2542 compactInputP0092542 hz 6
  rw [compactReplayP0092542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0092542, compactOutputP0092542,
    nodeZP0092541, nodeSP0092541, nodeEP0092541]

def compactInputP0102542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-230684447942438333698521) : ℚ) /
        461168601842738790400000000))

def compactOutputP0102542 : RatState2542 :=
  ((((118636477424989101 : ℚ) /
        1267650600228229401496703205376),
    (((-474914269751521) : ℚ) /
        158456325028528675187087900672)),
    ((15968934156557 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0102542 : compactExp2542 compactInputP0102542 6 = compactOutputP0102542 := by
  cbv

theorem compactErrorP0102542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0102541) - nodeSP0102541 6‖ ≤
      nodeEP0102541 6 := by
  have hz : ‖embedPair2542 compactInputP0102542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0102542]
  have h := compactExp_error2542 compactInputP0102542 hz 6
  rw [compactReplayP0102542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0102542, compactOutputP0102542,
    nodeZP0102541, nodeSP0102541, nodeEP0102541]

def compactInputP0112542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-255213677437476200797801) : ℚ) /
        461168601842738790400000000))

def compactOutputP0112542 : RatState2542 :=
  ((((59311428385533193 : ℚ) /
        633825300114114700748351602688),
    (((-525392938551263) : ℚ) /
        158456325028528675187087900672)),
    ((16014111615697 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0112542 : compactExp2542 compactInputP0112542 6 = compactOutputP0112542 := by
  cbv

theorem compactErrorP0112542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0112541) - nodeSP0112541 6‖ ≤
      nodeEP0112541 6 := by
  have hz : ‖embedPair2542 compactInputP0112542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0112542]
  have h := compactExp_error2542 compactInputP0112542 hz 6
  rw [compactReplayP0112542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0112542, compactOutputP0112542,
    nodeZP0112541, nodeSP0112541, nodeEP0112541]

def compactInputP0122542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-5612399119318874813509) : ℚ) /
        9223372036854775808000000))

def compactOutputP0122542 : RatState2542 :=
  ((((118607299907051495 : ℚ) /
        1267650600228229401496703205376),
    (((-4621360475007635) : ℚ) /
        1267650600228229401496703205376)),
    ((16060951127165 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0122542 : compactExp2542 compactInputP0122542 6 = compactOutputP0122542 := by
  cbv

theorem compactErrorP0122542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0122541) - nodeSP0122541 6‖ ≤
      nodeEP0122541 6 := by
  have hz : ‖embedPair2542 compactInputP0122542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0122542]
  have h := compactExp_error2542 compactInputP0122542 hz 6
  rw [compactReplayP0122542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0122542, compactOutputP0122542,
    nodeZP0122541, nodeSP0122541, nodeEP0122541]

def compactInputP0132542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-60754466143128272313291) : ℚ) /
        92233720368547758080000000))

def compactOutputP0132542 : RatState2542 :=
  ((((29647959775291545 : ℚ) /
        316912650057057350374175801344),
    (((-2501212830025299) : ℚ) /
        633825300114114700748351602688)),
    ((8051838237671 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

theorem compactReplayP0132542 : compactExp2542 compactInputP0132542 6 = compactOutputP0132542 := by
  cbv

theorem compactErrorP0132542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0132541) - nodeSP0132541 6‖ ≤
      nodeEP0132541 6 := by
  have hz : ‖embedPair2542 compactInputP0132542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0132542]
  have h := compactExp_error2542 compactInputP0132542 hz 6
  rw [compactReplayP0132542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0132542, compactOutputP0132542,
    nodeZP0132541, nodeSP0132541, nodeEP0132541]

def compactInputP0142542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-346671309892138695845011) : ℚ) /
        461168601842738790400000000))

def compactOutputP0142542 : RatState2542 :=
  ((((59279978025758391 : ℚ) /
        633825300114114700748351602688),
    (((-5708360968231559) : ℚ) /
        1267650600228229401496703205376)),
    ((16182945244379 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0142542 : compactExp2542 compactInputP0142542 6 = compactOutputP0142542 := by
  cbv

theorem compactErrorP0142542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0142541) - nodeSP0142541 6‖ ≤
      nodeEP0142541 6 := by
  have hz : ‖embedPair2542 compactInputP0142542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0142542]
  have h := compactExp_error2542 compactInputP0142542 hz 6
  rw [compactReplayP0142542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0142542, compactOutputP0142542,
    nodeZP0142541, nodeSP0142541, nodeEP0142541]

def compactInputP0152542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-377408574479356852679047) : ℚ) /
        461168601842738790400000000))

def compactOutputP0152542 : RatState2542 :=
  ((((118534527597542463 : ℚ) /
        1267650600228229401496703205376),
    (((-6214043056550585) : ℚ) /
        1267650600228229401496703205376)),
    ((16239823319829 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0152542 : compactExp2542 compactInputP0152542 6 = compactOutputP0152542 := by
  cbv

theorem compactErrorP0152542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0152541) - nodeSP0152541 6‖ ≤
      nodeEP0152541 6 := by
  have hz : ‖embedPair2542 compactInputP0152542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0152542]
  have h := compactExp_error2542 compactInputP0152542 hz 6
  rw [compactReplayP0152542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0152542, compactOutputP0152542,
    nodeZP0152541, nodeSP0152541, nodeEP0152541]

def compactInputP0162542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-199810861117846303095609) : ℚ) /
        230584300921369395200000000))

def compactOutputP0162542 : RatState2542 :=
  ((((59257404210677545 : ℚ) /
        633825300114114700748351602688),
    (((-6579418570870905) : ℚ) /
        1267650600228229401496703205376)),
    ((16280970021717 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0162542 : compactExp2542 compactInputP0162542 6 = compactOutputP0162542 := by
  cbv

theorem compactErrorP0162542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0162541) - nodeSP0162541 6‖ ≤
      nodeEP0162541 6 := by
  have hz : ‖embedPair2542 compactInputP0162542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0162542]
  have h := compactExp_error2542 compactInputP0162542 hz 6
  rw [compactReplayP0162542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0162542, compactOutputP0162542,
    nodeZP0162541, nodeSP0162541, nodeEP0162541]

def compactInputP0172542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-442769373018475956606027) : ℚ) /
        461168601842738790400000000))

def compactOutputP0172542 : RatState2542 :=
  ((((118473286804290763 : ℚ) /
        1267650600228229401496703205376),
    (((-7288955869634857) : ℚ) /
        1267650600228229401496703205376)),
    ((16360995261323 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0172542 : compactExp2542 compactInputP0172542 6 = compactOutputP0172542 := by
  cbv

theorem compactErrorP0172542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0172541) - nodeSP0172541 6‖ ≤
      nodeEP0172541 6 := by
  have hz : ‖embedPair2542 compactInputP0172542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0172542]
  have h := compactExp_error2542 compactInputP0172542 hz 6
  rw [compactReplayP0172542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0172542, compactOutputP0172542,
    nodeZP0172541, nodeSP0172541, nodeEP0172541]

def compactInputP0182542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-114770645411675231749613) : ℚ) /
        115292150460684697600000000))

def compactOutputP0182542 : RatState2542 :=
  ((((118456481654819807 : ℚ) /
        1267650600228229401496703205376),
    (((-944643764225425) : ℚ) /
        158456325028528675187087900672)),
    ((16391285394785 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0182542 : compactExp2542 compactInputP0182542 6 = compactOutputP0182542 := by
  cbv

theorem compactErrorP0182542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0182541) - nodeSP0182541 6‖ ≤
      nodeEP0182541 6 := by
  have hz : ‖embedPair2542 compactInputP0182542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0182542]
  have h := compactExp_error2542 compactInputP0182542 hz 6
  rw [compactReplayP0182542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0182542, compactOutputP0182542,
    nodeZP0182541, nodeSP0182541, nodeEP0182541]

def compactInputP0192542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-24428249467783476683391) : ℚ) /
        23058430092136939520000000))

def compactOutputP0192542 : RatState2542 :=
  ((((118424570111872407 : ℚ) /
        1267650600228229401496703205376),
    (((-62826178984837) : ℚ) /
        9903520314283042199192993792)),
    ((16446075308529 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0192542 : compactExp2542 compactInputP0192542 6 = compactOutputP0192542 := by
  cbv

theorem compactErrorP0192542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0192541) - nodeSP0192541 6‖ ≤
      nodeEP0192541 6 := by
  have hz : ‖embedPair2542 compactInputP0192542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0192542]
  have h := compactExp_error2542 compactInputP0192542 hz 6
  rw [compactReplayP0192542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0192542, compactOutputP0192542,
    nodeZP0192541, nodeSP0192541, nodeEP0192541]

def compactInputP0202542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-520624750538575899551419) : ℚ) /
        461168601842738790400000000))

def compactOutputP0202542 : RatState2542 :=
  ((((59193809433560839 : ℚ) /
        633825300114114700748351602688),
    (((-4284281236519013) : ℚ) /
        633825300114114700748351602688)),
    ((16505723794689 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0202542 : compactExp2542 compactInputP0202542 6 = compactOutputP0202542 := by
  cbv

theorem compactErrorP0202542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0202541) - nodeSP0202541 6‖ ≤
      nodeEP0202541 6 := by
  have hz : ‖embedPair2542 compactInputP0202542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0202542]
  have h := compactExp_error2542 compactInputP0202542 hz 6
  rw [compactReplayP0202542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0202542, compactOutputP0202542,
    nodeZP0202541, nodeSP0202541, nodeEP0202541]

def compactInputP0212542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-547379874475946380671387) : ℚ) /
        461168601842738790400000000))

def compactOutputP0212542 : RatState2542 :=
  ((((118354987626893989 : ℚ) /
        1267650600228229401496703205376),
    (((-2252019478698383) : ℚ) /
        316912650057057350374175801344)),
    ((8277778649227 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

theorem compactReplayP0212542 : compactExp2542 compactInputP0212542 6 = compactOutputP0212542 := by
  cbv

theorem compactErrorP0212542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0212541) - nodeSP0212541 6‖ ≤
      nodeEP0212541 6 := by
  have hz : ‖embedPair2542 compactInputP0212542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0212542]
  have h := compactExp_error2542 compactInputP0212542 hz 6
  rw [compactReplayP0212542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0212542, compactOutputP0212542,
    nodeZP0212541, nodeSP0212541, nodeEP0212541]

def compactInputP0222542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-112214826711468142236233) : ℚ) /
        92233720368547758080000000))

def compactOutputP0222542 : RatState2542 :=
  ((((924512925072633 : ℚ) /
        9903520314283042199192993792),
    (((-9232990457430623) : ℚ) /
        1267650600228229401496703205376)),
    ((16581082998613 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0222542 : compactExp2542 compactInputP0222542 6 = compactOutputP0222542 := by
  cbv

theorem compactErrorP0222542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0222541) - nodeSP0222541 6‖ ≤
      nodeEP0222541 6 := by
  have hz : ‖embedPair2542 compactInputP0222542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0222542]
  have h := compactExp_error2542 compactInputP0222542 hz 6
  rw [compactReplayP0222542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0222542, compactOutputP0222542,
    nodeZP0222541, nodeSP0222541, nodeEP0222541]

def compactInputP0232542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-300278613592663314364333) : ℚ) /
        230584300921369395200000000))

def compactOutputP0232542 : RatState2542 :=
  ((((118285287142593757 : ℚ) /
        1267650600228229401496703205376),
    (((-9881265580651307) : ℚ) /
        1267650600228229401496703205376)),
    ((16654750164649 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0232542 : compactExp2542 compactInputP0232542 6 = compactOutputP0232542 := by
  cbv

theorem compactErrorP0232542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0232541) - nodeSP0232541 6‖ ≤
      nodeEP0232541 6 := by
  have hz : ‖embedPair2542 compactInputP0232542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0232542]
  have h := compactExp_error2542 compactInputP0232542 hz 6
  rw [compactReplayP0232542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0232542, compactOutputP0232542,
    nodeZP0232541, nodeSP0232541, nodeEP0232541]

def compactInputP0242542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-309351029057948556428147) : ℚ) /
        230584300921369395200000000))

def compactOutputP0242542 : RatState2542 :=
  ((((29565007532342975 : ℚ) /
        316912650057057350374175801344),
    (((-10179088253928775) : ℚ) /
        1267650600228229401496703205376)),
    ((521520005383 : ℚ) /
        (4 * 10^40
        + 3556142965880123323311949751266331066368)))

theorem compactReplayP0242542 : compactExp2542 compactInputP0242542 6 = compactOutputP0242542 := by
  cbv

theorem compactErrorP0242542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0242541) - nodeSP0242541 6‖ ≤
      nodeEP0242541 6 := by
  have hz : ‖embedPair2542 compactInputP0242542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0242542]
  have h := compactExp_error2542 compactInputP0242542 hz 6
  rw [compactReplayP0242542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0242542, compactOutputP0242542,
    nodeZP0242541, nodeSP0242541, nodeEP0242541]

def compactInputP0252542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-10022692915539018190833) : ℚ) /
        7205759403792793600000000))

def compactOutputP0252542 : RatState2542 :=
  ((((118227302975125153 : ℚ) /
        1267650600228229401496703205376),
    (((-10552411814802503) : ℚ) /
        1267650600228229401496703205376)),
    ((16731163451757 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0252542 : compactExp2542 compactInputP0252542 6 = compactOutputP0252542 := by
  cbv

theorem compactErrorP0252542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0252541) - nodeSP0252541 6‖ ≤
      nodeEP0252541 6 := by
  have hz : ‖embedPair2542 compactInputP0252542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0252542]
  have h := compactExp_error2542 compactInputP0252542 hz 6
  rw [compactReplayP0252542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0252542, compactOutputP0252542,
    nodeZP0252541, nodeSP0252541, nodeEP0252541]

def compactInputP0262542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-20771944281655350607437) : ℚ) /
        14411518807585587200000000))

def compactOutputP0262542 : RatState2542 :=
  ((((29548159886751887 : ℚ) /
        316912650057057350374175801344),
    (((-10933824618694401) : ℚ) /
        1267650600228229401496703205376)),
    ((16774656448449 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0262542 : compactExp2542 compactInputP0262542 6 = compactOutputP0262542 := by
  cbv

theorem compactErrorP0262542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0262541) - nodeSP0262541 6‖ ≤
      nodeEP0262541 6 := by
  have hz : ‖embedPair2542 compactInputP0262542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0262542]
  have h := compactExp_error2542 compactInputP0262542 hz 6
  rw [compactReplayP0262542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0262542, compactOutputP0262542,
    nodeZP0262541, nodeSP0262541, nodeEP0262541]

def compactInputP0272542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-43640783619197408678627) : ℚ) /
        28823037615171174400000000))

def compactOutputP0272542 : RatState2542 :=
  ((((118140450249691527 : ℚ) /
        1267650600228229401496703205376),
    (((-11484014049163365) : ℚ) /
        1267650600228229401496703205376)),
    ((8418740926875 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

theorem compactReplayP0272542 : compactExp2542 compactInputP0272542 6 = compactOutputP0272542 := by
  cbv

theorem compactErrorP0272542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0272541) - nodeSP0272541 6‖ ≤
      nodeEP0272541 6 := by
  have hz : ‖embedPair2542 compactInputP0272542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0272542]
  have h := compactExp_error2542 compactInputP0272542 hz 6
  rw [compactReplayP0272542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0272542, compactOutputP0272542,
    nodeZP0272541, nodeSP0272541, nodeEP0272541]

def compactInputP0282542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-177883892884016178388727) : ℚ) /
        115292150460684697600000000))

def compactOutputP0282542 : RatState2542 :=
  ((((14764885000630055 : ℚ) /
        158456325028528675187087900672),
    (((-5850886741428091) : ℚ) /
        633825300114114700748351602688)),
    ((16862375930733 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplayP0282542 : compactExp2542 compactInputP0282542 6 = compactOutputP0282542 := by
  cbv

theorem compactErrorP0282542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0282541) - nodeSP0282541 6‖ ≤
      nodeEP0282541 6 := by
  have hz : ‖embedPair2542 compactInputP0282542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0282542]
  have h := compactExp_error2542 compactInputP0282542 hz 6
  rw [compactReplayP0282542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0282542, compactOutputP0282542,
    nodeZP0282541, nodeSP0282541, nodeEP0282541]

def compactInputP0292542 : RatPair2542 :=
  ((((-((385461 * 10^40
        + 922357162940632251641364347660380013052) * 10^40
        + 2982951078097679254971542802580499052933)) : ℚ) /
        ((822334 * 10^40
        + 3994872583325805755132375033112881246178) * 10^40
        + 9431483824563824370319589815091200000000)),
    (((-182939534351242879487659) : ℚ) /
        115292150460684697600000000))

def compactOutputP0292542 : RatState2542 :=
  ((((29521443626647347 : ℚ) /
        316912650057057350374175801344),
    (((-12033221640946533) : ℚ) /
        1267650600228229401496703205376)),
    ((8450148954553 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

theorem compactReplayP0292542 : compactExp2542 compactInputP0292542 6 = compactOutputP0292542 := by
  cbv

theorem compactErrorP0292542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0292541) - nodeSP0292541 6‖ ≤
      nodeEP0292541 6 := by
  have hz : ‖embedPair2542 compactInputP0292542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInputP0292542]
  have h := compactExp_error2542 compactInputP0292542 hz 6
  rw [compactReplayP0292542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInputP0292542, compactOutputP0292542,
    nodeZP0292541, nodeSP0292541, nodeEP0292541]

end ConnesWeilRH.Dev
#print axioms ConnesWeilRH.Dev.compactErrorP0002542
#print axioms ConnesWeilRH.Dev.compactErrorP0012542
#print axioms ConnesWeilRH.Dev.compactErrorP0022542
#print axioms ConnesWeilRH.Dev.compactErrorP0032542
#print axioms ConnesWeilRH.Dev.compactErrorP0042542
#print axioms ConnesWeilRH.Dev.compactErrorP0052542
#print axioms ConnesWeilRH.Dev.compactErrorP0062542
#print axioms ConnesWeilRH.Dev.compactErrorP0072542
#print axioms ConnesWeilRH.Dev.compactErrorP0082542
#print axioms ConnesWeilRH.Dev.compactErrorP0092542
#print axioms ConnesWeilRH.Dev.compactErrorP0102542
#print axioms ConnesWeilRH.Dev.compactErrorP0112542
#print axioms ConnesWeilRH.Dev.compactErrorP0122542
#print axioms ConnesWeilRH.Dev.compactErrorP0132542
#print axioms ConnesWeilRH.Dev.compactErrorP0142542
#print axioms ConnesWeilRH.Dev.compactErrorP0152542
#print axioms ConnesWeilRH.Dev.compactErrorP0162542
#print axioms ConnesWeilRH.Dev.compactErrorP0172542
#print axioms ConnesWeilRH.Dev.compactErrorP0182542
#print axioms ConnesWeilRH.Dev.compactErrorP0192542
#print axioms ConnesWeilRH.Dev.compactErrorP0202542
#print axioms ConnesWeilRH.Dev.compactErrorP0212542
#print axioms ConnesWeilRH.Dev.compactErrorP0222542
#print axioms ConnesWeilRH.Dev.compactErrorP0232542
#print axioms ConnesWeilRH.Dev.compactErrorP0242542
#print axioms ConnesWeilRH.Dev.compactErrorP0252542
#print axioms ConnesWeilRH.Dev.compactErrorP0262542
#print axioms ConnesWeilRH.Dev.compactErrorP0272542
#print axioms ConnesWeilRH.Dev.compactErrorP0282542
#print axioms ConnesWeilRH.Dev.compactErrorP0292542
