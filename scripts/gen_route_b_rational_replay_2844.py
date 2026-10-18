#!/usr/bin/env python3
"""Generate the exact order-7 rational replay source for cell 4096."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = json.loads((ROOT / "results/2840_route_b_cell4096_stage_bridge.json").read_text())
OUT = ROOT / "ConnesWeilRH/Dev/C1RouteBRationalReplay2844.lean"


def rat(s):
    a, b = s.split("/")
    return f"({a} : ℚ) / {b}"


def box(stage, k):
    z = DATA["orders"]["7"][stage][k]
    return "{ lo := %s, hi := %s, ordered := by norm_num }" % (rat(z["lo"]), rat(z["hi"]))


def fn(name, stage):
    lines = [f"def {name} (n : ℕ) : RationalBox2744 :=", "  match n with"]
    lines += [f"  | {k} => {box(stage, k)}" for k in range(8)]
    lines += ["  | _ => RationalBox2744.zero", ""]
    return "\n".join(lines)


text = '''import ConnesWeilRH.Dev.C1RationalExponentialJet2750
import ConnesWeilRH.Dev.C1RationalReciprocalJet2748

namespace ConnesWeilRH.Dev
noncomputable section

'''
for name, stage in [("routeBPhase2844", "phase"), ("routeBExp2844", "exp"),
                    ("routeBDenominator2844", "denominator"),
                    ("routeBReciprocal2844", "reciprocal"),
                    ("routeBTransition2844", "transition")]:
    text += fn(name, stage)
text += '''
def routeBReplayExp2844 : ℕ → RationalBox2744 :=
  rationalExponentialJet2750 routeBPhase2844 (routeBExp2844 0)

def routeBReplayDenominator2844 : ℕ → RationalBox2744 :=
  fun n => if n = 0 then RationalBox2744.add (routeBReplayExp2844 0)
    { lo := 1, hi := 1, ordered := by norm_num }
    else routeBReplayExp2844 n

def routeBReplayReciprocal2844 : ℕ → RationalBox2744 :=
  rationalReciprocalJet2748 routeBReplayDenominator2844 (by
    norm_num [routeBReplayDenominator2844, routeBReplayExp2844,
      rationalExponentialJet2750, routeBPhase2844, routeBExp2844,
      RationalBox2744.sum, RationalBox2744.zero, RationalBox2744.add,
      RationalBox2744.mul, RationalBox2744.nsmul])

def routeBReplayTransition2844 : RationalBox2744 :=
  rationalProductJet2747 routeBReplayExp2844 routeBReplayReciprocal2844 7

def routeBBoxContained2844 (a b : RationalBox2744) : Prop :=
  b.lo ≤ a.lo ∧ a.hi ≤ b.hi

theorem routeB_replay_transition_contained2844 :
    routeBBoxContained2844 routeBReplayTransition2844 (routeBTransition2844 7) := by
  norm_num [Nat.choose, routeBBoxContained2844, routeBReplayTransition2844,
    routeBReplayExp2844, routeBReplayDenominator2844,
    routeBReplayReciprocal2844, rationalExponentialJet2750,
    rationalReciprocalJet2748, rationalProductJet2747,
    RationalBox2744.sum, RationalBox2744.zero, RationalBox2744.add,
    RationalBox2744.sub, RationalBox2744.mul, RationalBox2744.nsmul,
    RationalBox2744.invPositive, routeBPhase2844, routeBExp2844,
    routeBDenominator2844, routeBReciprocal2844, routeBTransition2844]

end
end ConnesWeilRH.Dev
'''
OUT.write_text(text, encoding="utf-8")
print(OUT)
