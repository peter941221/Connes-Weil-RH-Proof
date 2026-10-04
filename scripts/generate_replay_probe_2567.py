"""Replay-mechanism gate probe (record 2567): cbv vs decide vs rfl.

Derives three 30-family exponential-replay modules from the accepted
C1RouteAPairedN05440Plus2553 node module. All three keep identical
definitions, statements and imports; only the tactic closing the
compactExp2547 equality varies. This is the 2553/2554 open decision:
whichever kernel mechanism proves the replay equalities cheapest sets the
generation volume of the full-grid batch lanes 2b-2d.
"""
import re

from generate_complex_exp_node_2541 import ROOT
from format_lean_source_2553 import wrap_source

BASE = "C1RouteAPairedN05440Plus2553"
TACTICS = ("Cbv", "Decide", "Rfl")


def render(tactic):
    assert tactic in TACTICS
    source = (ROOT / f"ConnesWeilRH/Dev/{BASE}.lean").read_text(encoding="utf-8")
    source = source[:source.index("#print axioms")]
    low = tactic.lower()
    for i in range(30):
        prefix = f"pairedN05440PlusP{i:03d}"
        pattern = r"theorem " + prefix + r"BaseError2553.*?(?=\n(?:theorem|def|noncomputable def|end) )"
        base = re.search(pattern, source, re.S)[0]
        state = re.search(r"  have hs :(.*?)\n  have hc", base, re.S)[1]
        head, sep, closing = state.rpartition(":= by ")
        assert sep and closing.strip() == "cbv", (i, closing)
        swapped = head + f":= by {low}\n"
        source = source.replace(base, f"theorem {prefix}Replay2553 :{swapped}")
        pattern = r"theorem " + prefix + r"DerivativeError2553.*?(?=\n(?:theorem|def|noncomputable def|end) )"
        source, count = re.subn(pattern, "", source, count=1, flags=re.S)
        assert count == 1
    # 2553 incident invariant: renaming moves nothing but the name tokens.
    # Compare the non-name remainder before and after the rename.
    remainder_before = re.sub(r"pairedN05440Plus\w*2553", "", source)
    source = re.sub(r"\bpairedN05440Plus(\w*)2553\b",
                    lambda m: "probe" + tactic + m[1] + "2567", source)
    assert "pairedN05440Plus" not in source
    remainder_after = re.sub(r"probe" + tactic + r"\w*2567", "", source)
    assert remainder_before == remainder_after, "digit drift under rename"
    for i in range(30):
        source += f"#print axioms ConnesWeilRH.Dev.probe{tactic}P{i:03d}Replay2567\n"
    return wrap_source(source)


if __name__ == "__main__":
    for tactic in TACTICS:
        out = render(tactic)
        target = ROOT / f"ConnesWeilRH/Dev/C1RouteAReplayProbe{tactic}2567.lean"
        target.write_text(out, encoding="utf-8", newline="\n")
        print(f"REPLAY_PROBE_{tactic}_GENERATED", len(out.encode()), flush=True)
