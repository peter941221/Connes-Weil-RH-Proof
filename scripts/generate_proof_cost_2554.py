"""Cumulative phase timings on the same accepted full 30-family node."""
import re

from generate_complex_exp_node_2541 import ROOT
from format_lean_source_2553 import wrap_source


def render(mode):
    source = (ROOT/"ConnesWeilRH/Dev/C1RouteAPairedN05440Plus2553.lean").read_text(encoding="utf-8")
    source = source[:source.index("#print axioms")]
    for i in range(30):
        prefix = f"pairedN05440PlusP{i:03d}"
        pattern = r"theorem "+prefix+r"BaseError2553.*?(?=\n(?:theorem|def|noncomputable def|end) )"
        base = re.search(pattern,source,re.S)[0]
        if mode == "Replay":
            state = re.search(r"  have hs :(.*?)\n  have hc",base,re.S)[1]
            source = source.replace(base,f"theorem {prefix}Replay2553 :{state}\n")
        if mode != "Full":
            pattern = r"theorem "+prefix+r"DerivativeError2553.*?(?=\n(?:theorem|def|noncomputable def|end) )"
            source,count = re.subn(pattern,"",source,count=1,flags=re.S)
            assert count == 1
    source = re.sub(r"\bpairedN05440Plus(\w*)2553\b",lambda m:"profile"+mode+m[1]+"2554",source)
    suffix = {"Replay":"Replay","Base":"BaseError","Full":"DerivativeError"}[mode]
    for i in range(30):
        source += f"#print axioms ConnesWeilRH.Dev.profile{mode}P{i:03d}{suffix}2554\n"
    return wrap_source(source)


if __name__ == "__main__":
    for mode in ("Replay","Base","Full"):
        source = render(mode)
        (ROOT/f"ConnesWeilRH/Dev/C1RouteAProfile{mode}2554.lean").write_text(source,encoding="utf-8",newline="\n")
        print(mode,len(source.encode()),flush=True)
