import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteAExpNode2541P000

namespace ConnesWeilRH.Dev

def compactInput2542 : RatPair2542 :=
  ((((-((263275 * 10^40
        + 1125171558294111539978267023056917167198) * 10^40
        + 1332055800215011207425642192228936552933)) : ℚ) /
        ((561665 * 10^40
        + 4151492452771926362187803248812537956572) * 10^40
        + 1774117228738064370319589815091200000000)), (((-362039942185747774262029) : ℚ) /
        461168601842738790400000000))

def compactExpected2542 : RatState2542 :=
  ((((1852300462860835 : ℚ) /
        19807040628566084398385987584), (((-1490300349709075) : ℚ) /
        316912650057057350374175801344)), ((16211342998361 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

theorem compactReplay2542 :
    compactExp2542 compactInput2542 6 = compactExpected2542 := by
  decide +kernel

theorem compactReplay_error2542 :
    ‖Complex.exp ((2 : ℂ)^6 * nodeZP0002541) - nodeSP0002541 6‖ ≤ nodeEP0002541 6 := by
  have hz : ‖embedPair2542 compactInput2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, compactInput2542]
  have h := compactExp_error2542 compactInput2542 hz 6
  rw [compactReplay2542] at h
  convert h using 1 <;> norm_num [embedPair2542, compactInput2542, compactExpected2542,
    nodeZP0002541, nodeSP0002541, nodeEP0002541]

end ConnesWeilRH.Dev
