CONTENT = "import ConnesWeilRH.Dev.Wall14PlateauBounds\n\n"
CONTENT += "namespace ConnesWeilRH\nnamespace Source\nnamespace Dev\nnamespace Wall14Plateau\n\n"
CONTENT += "open MeasureTheory\nopen scoped Topology\nopen Filter Set\n\n"
CONTENT += "/-! Integral assembly for the hI closure.  RH NOT claimed. -/\n\n"
CONTENT += "lemma int_tail_gate_le (R : Real) (hR : 2 <= R) :\n"
CONTENT += "    (∫ y in Ioi R, |plateauArchG y|) <=\n"
CONTENT += "        (2 * plateauA) * ((1 / tailC) * Real.exp (-R)) := by\n"
CONTENT_HAS_LEM = False
CONTENT += "  sorry\n\n"
CONTENT += "end Wall14Plateau\nend Dev\nend Source\nend ConnesWeilRH\n"
with open("ConnesWeilRH/Dev/Wall14PlateauIntegrateH.lean", "w", encoding="utf-8", newline="\n") as f:
    f.write(CONTENT)
print("wrote with 'sorry' placeholder - NOT final")
