"""Matched-import cost probe: separate versus paired exact state replays.

Actual order-three production derivatives, not a whole-cell certificate.
"""
import json
import re

from generate_boundary_replay_2547 import ROOT, render
from validate_boundary_replay_2547 import check
from format_lean_source_2553 import wrap_source


def main():
    cases = [(2701, 1), (2701, 15), (5440, 1), (5440, 15)]
    sources = {"Separate": [], "Paired": []}
    readings = []
    header = None
    for number, (index, family) in enumerate(cases):
        source, _ = render(grid_index=index, family_index=family)
        reading = check(source, family_index=family, grid_indices=(index,))
        readings.append(reading)
        prefix, body = source.split("namespace ConnesWeilRH.Dev\n", 1)
        header = prefix
        body = body[:body.index("end ConnesWeilRH.Dev")]
        start = body.index("  have hc :")
        end = body.index("  have h := compactExp_error2547", start)
        rational = re.search(r"have hq :.*?=\s*(.*?) := by cbv", body[start:end], re.S)[1]
        depth = reading["depth"]
        replacement = f"""  have hs : compactExp2547 boundaryInput2547 {depth} =
      (boundaryCenter2547, {rational}) := by cbv
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 boundaryInput2547 {depth}).2 : ℝ) = boundaryError2547 := by
    rw [hs]
    norm_num [boundaryError2547]
"""
        paired = body[:start] + replacement + body[end:]
        for mode, text in (("Separate", body), ("Paired", paired)):
            text = text.replace("boundary", f"batch{mode}C{number:03d}")
            sources[mode].append(text)
    target = ROOT / "ConnesWeilRH/Dev"
    baseline = header + "namespace ConnesWeilRH.Dev\nend ConnesWeilRH.Dev\n"
    (target / "C1RouteABatchBaseline2552.lean").write_text(baseline, encoding="utf-8", newline="\n")
    for mode, bodies in sources.items():
        text = header + "namespace ConnesWeilRH.Dev\n" + "\n".join(bodies)
        text += "end ConnesWeilRH.Dev\n"
        for number in range(len(cases)):
            for suffix in ("BaseError", "ThirdError"):
                text += f"#print axioms ConnesWeilRH.Dev.batch{mode}C{number:03d}{suffix}2547\n"
        (target / f"C1RouteABatch{mode}2552.lean").write_text(wrap_source(text), encoding="utf-8", newline="\n")
    result = dict(record=2552, scope="four actual order-three family evaluations at sigma+1/2",
                  cases=readings, formal_build_verified=False, full_grid_certificate=False)
    (ROOT / "results/2552_batch_cost_inputs.json").write_text(json.dumps(result, indent=2)+"\n")
    print("BATCH_COST_INPUTS_PASS", len(cases), flush=True)


if __name__ == "__main__":
    main()
