"""Instantiate the accepted compact evaluator at 160 coordinate bits."""
from generate_complex_exp_node_2541 import ROOT


def render():
    old = (ROOT/"ConnesWeilRH/Dev/C1RouteACompactExp2542.lean").read_text()
    body = old[old.index("theorem embedPair_round_error2542"):old.index("end ConnesWeilRH.Dev")]
    for name in ("embedPair_round_error","pairRound","rounding","hornerRat_error","hornerRat",
                 "initialState_error","initialState","squareState_error","squareState",
                 "compactExp_error","compactExp"):
        body = body.replace(name+"2542",name+"2547")
    body = body.replace(" 100", " 160").replace("^ 100", "^ 160").replace(" 140", " 200")
    return """import ConnesWeilRH.Dev.C1RouteACompactExp2542

/-! The same rounded-Horner/squaring algorithm with 160-bit coordinates.
The base Taylor allowance is unchanged; state radii round upward at 200 bits. -/

namespace ConnesWeilRH.Dev

def pairRound2547 (a : RatPair2542) : RatPair2542 :=
  (roundDown2542 160 a.1, roundDown2542 160 a.2)

def rounding2547 : ℚ := 1 / 2 ^ 159

"""+body+"""end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.embedPair_round_error2547
#print axioms ConnesWeilRH.Dev.hornerRat_error2547
#print axioms ConnesWeilRH.Dev.squareState_error2547
#print axioms ConnesWeilRH.Dev.compactExp_error2547
"""


if __name__ == "__main__":
    (ROOT/"ConnesWeilRH/Dev/C1RouteACompactExp1602547.lean").write_text(
        render(),encoding="utf-8",newline="\n")
    print("COMPACT_EXP160_GENERATED",flush=True)
