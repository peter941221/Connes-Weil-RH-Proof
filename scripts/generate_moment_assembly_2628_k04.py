"""Regenerate the owner-04 (K04) moment-assembly probe ZProbe2628K04.

The owner-00 template ZProbe2628Sum.lean was never compile-verified: the
2026-10-09 rebuild (record 2634) showed transplanted owner-00 values in
every numeric position. This generator therefore re-derives every numeric
fact from the K04 sources instead of trusting template literals:

- per-panel centers from the K04 panel tables,
- per-panel error exponents from the K04 actual-panel certificates,
- the entry-04 edge charge from the K04 actual-edge certificate,
- the row-04 interval endpoints from the 2597 module.

It also emits the missing real-side error bridge
(actualFullRealError2628K04) and a corrected membership proof.
"""
import re
import sys
from fractions import Fraction
from pathlib import Path

sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH" / "Dev"


def read_panel_data():
    centers = []
    exponents = []
    for panel in range(180):
        table = (DEV / f"C1RouteAMomentPanelTable2622K04Panel{panel:03d}.lean").read_text(encoding="utf-8")
        center_match = re.search(rf"def momentPanelIntegralCenter2622K04P{panel:03d} : .*? := \(\((\d+) .*? / (\d+)", table)
        if center_match is None:
            raise RuntimeError(f"missing owner-04 center for panel {panel}")
        centers.append(Fraction(int(center_match[1]), int(center_match[2])))
        actual = (DEV / f"C1RouteAMomentActualPanel2622K04Panel{panel:03d}.lean").read_text(encoding="utf-8")
        exponent_match = re.search(rf"actualMomentPanelK04{panel:03d}_integral_error_le2622[\s\S]*?/ 10 \^ (\d+)", actual)
        if exponent_match is None:
            raise RuntimeError(f"missing owner-04 error exponent for panel {panel}")
        exponents.append(int(exponent_match[1]))
    edge_source = (DEV / "C1RouteAMomentActualEdge2620K04.lean").read_text(encoding="utf-8")
    edge_match = re.search(r"actualMomentEntry04_bothEdgeCharge_le2620[\s\S]*?\(\s*(\d+)\s*:\s*ℝ\s*\)\s*/\s*10 \^ (\d+)", edge_source)
    if edge_match is None:
        raise RuntimeError("missing owner-04 edge charge")
    edge_charge = (int(edge_match.group(1)), int(edge_match.group(2)))
    intervals = (DEV / "C1RouteACorrectionAnalyticIntervals2597.lean").read_text(encoding="utf-8")
    row04_start = intervals.index("noncomputable def analyticMomentInterval2597_row_04")
    row04_end = intervals.index("noncomputable def analyticMomentInterval2597_row_05", row04_start)
    row04 = intervals[row04_start:row04_end]
    # entry (4,4) is the FIFTH element of row_04; a first-match regex here
    # silently returns element 1 (record-2634 lesson - all micro variants
    # v1 targeted the wrong fraction on top of the peel stall).
    re_los = re.findall(r"reLo := \(\((-?\d+) : ℝ\) / (\d+)\)", row04)
    re_his = re.findall(r"reHi := \(\((-?\d+) : ℝ\) / (\d+)\)", row04)
    if len(re_los) != 30 or len(re_his) != 30:
        raise RuntimeError(f"row-04 endpoint scan found {len(re_los)}/{len(re_his)}, expected 30")
    re_lo, re_hi = re_los[4], re_his[4]
    endpoints = {
        "lo": (int(re_lo[0]), int(re_lo[1])),
        "hi": (int(re_hi[0]), int(re_hi[1])),
    }
    return centers, exponents, edge_charge, endpoints


def read_entry44() -> dict:
    """Row-04 element 5 (entry (4,4)) verbatim from the 2597 source.

    Returns the re-indented whole-element text plus the four verbatim
    field texts. The kernel-rfl bridges only close when the right-hand
    sides are the SAME literal terms the 2597 module elaborated: simp
    peeling of the matrix application stalls at index 4 (micro campaign
    2634), so every consumer goes through a verbatim copy instead.
    """
    src = (DEV / "C1RouteACorrectionAnalyticIntervals2597.lean").read_text(encoding="utf-8")
    match = re.search(
        r"noncomputable def analyticMomentInterval2597_row_04 : Fin 30 → ComplexRect2427 :=\s*\n\s*!\[(.*?)\]\s*$",
        src, re.S | re.M)
    if match is None:
        raise RuntimeError("missing row_04 matrix literal")
    body = match.group(1)
    elems, depth, start = [], 0, None
    for i, ch in enumerate(body):
        if ch == "{":
            if depth == 0:
                start = i
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                elems.append(body[start:i + 1])
    if len(elems) != 30:
        raise RuntimeError(f"row_04 parse found {len(elems)} elements, expected 30")
    element = elems[4].strip()
    lines = element.splitlines()
    fields = {}
    for i, name in enumerate(("reLo", "reHi", "imLo", "imHi")):
        field_match = re.search(re.escape(name) + r" := (.+?)(,?)$", lines[i].strip())
        if field_match is None:
            raise RuntimeError(f"missing field {name} in row_04 element 5")
        # the imHi line ends with the element's closing brace; a field
        # value itself never ends with ',' or '}' (numerals, parens, /)
        fields[name] = field_match.group(1).rstrip(",}")
    # Continuation lines MUST keep their original deep indentation: a
    # field token at the same column as the opening '{' makes the
    # structure parser close the literal early (unexpected identifier;
    # expected '}') - the v9 rendering incident.
    indented = lines[0].strip() + "\n" + "\n".join("    " + line for line in lines[1:])
    return {"element": indented, "fields": fields}


def nested_eps_sum(edge_charge: tuple, exponents) -> str:
    """((edge)) + ((1/10^e0) + ((1/10^e1) + (...))) as a Lean Q expression."""
    expr = f"((1 : ℚ) / 10 ^ {exponents[-1]})"
    for exponent in reversed(exponents[:-1]):
        expr = f"({expr} + ((1 : ℚ) / 10 ^ {exponent}))"
    return f"((({edge_charge[0]} : ℚ) / 10 ^ {edge_charge[1]})) + {expr}"


def replace_theorem_block(source: str, name: str, body: str) -> str:
    start = source.index(f"theorem {name} :")
    next_theorem = source.find("\ntheorem ", start + 1)
    if next_theorem < 0:
        next_theorem = source.index("\nend ConnesWeilRH.Dev")
    return source[:start] + body + source[next_theorem + 1:]


def replace_replay_value(source: str, theorem_name: str, value: Fraction) -> str:
    """Replace the decimal-fraction right-hand side of a replay theorem."""
    pattern = rf"(theorem {theorem_name} :[^=]+=)\s*\(\((\d+) : ℚ\) / (\d+)\)"
    replacement = rf"\g<1> (( {value.numerator} : ℚ) / {value.denominator})"
    new_source, count = re.subn(pattern, replacement, source, count=1)
    if count != 1:
        raise RuntimeError(f"cannot rewrite replay value of {theorem_name}")
    return new_source


def main():
    centers, exponents, edge_charge, endpoints = read_panel_data()
    edge_fraction = Fraction(edge_charge[0], 10 ** edge_charge[1])
    total = sum(centers, Fraction())
    eps = edge_fraction + sum((Fraction(1, 10 ** exponent) for exponent in exponents), Fraction())
    lo_q = total - eps
    hi_q = total + eps
    chunk_totals = [
        sum(centers[chunk * 30:(chunk + 1) * 30], Fraction())
        for chunk in range(6)
    ]
    eps_chunks = [
        sum((Fraction(1, 10 ** exponents[p]) for p in range(chunk * 30, (chunk + 1) * 30)), Fraction())
        for chunk in range(6)
    ]
    eps_from_chunks = edge_fraction + sum(eps_chunks, Fraction())
    if eps_from_chunks != eps:
        raise RuntimeError("chunked eps disagrees with the nested eps sum")
    entry44 = read_entry44()
    entry44_fields = entry44["fields"]
    entry44_text = entry44["element"]

    source = (DEV / "ZProbe2628Sum.lean").read_text(encoding="utf-8")
    source = re.sub(r"C1RouteAMomentActualPanel2622Panel([0-9]{3})", r"C1RouteAMomentActualPanel2622K04Panel\1", source)
    source = re.sub(r"actualMomentPanel([0-9]{3})_integral_error_le2622", r"actualMomentPanelK04\1_integral_error_le2622", source)
    replacements = {
        "momentPanelIntegralCenter2622P": "momentPanelIntegralCenter2622K04P",
        "storedWidth 0": "storedWidth 4",
        "capturedNodes2584 0": "capturedNodes2584 4",
        "analyticMomentInterval2597 0 0": "analyticMomentInterval2597 4 4",
        "analyticMomentInterval2597_row_00": "analyticMomentInterval2597_row_04",
        "partitionCenter2628": "partitionCenter2628K04",
        "chunkCenters_replay2628": "chunkCenters_replay2628K04",
        "chunkCenters2628": "chunkCenters2628K04",
        "dec2628": "dec2628K04",
        "panelIntegral2628": "panelIntegral2628K04",
        "panelError2628": "panelError2628K04",
        "totalCenters2628": "totalCenters2628K04",
        "panelIntegrals2628_sum_eq_global": "panelIntegrals2628K04_sum_eq_global",
        "panelErrorSum2628": "panelErrorSum2628K04",
        "totalCenters_replay2628": "totalCenters_replay2628K04",
        "probeEpsReplay2628": "probeEpsReplay2628K04",
        "probeFinalLo2628": "probeFinalLo2628K04",
        "probeFinalHi2628": "probeFinalHi2628K04",
        "probeCloseLo2628": "probeCloseLo2628K04",
        "probeCloseHi2628": "probeCloseHi2628K04",
    }
    for old, new in replacements.items():
        source = source.replace(old, new)

    # Backfill the per-panel exponent branches: the template's dec2628
    # branches carry owner-00 exponents, which do not match the regenerated
    # K04 panel certificates (record 2634 incident - type mismatch at
    # panelError2628K04_XXX because the K04 modules prove strictly tighter
    # bounds than the transplanted branches claim).
    dec_start = source.index("def dec2628K04 : ℕ → ℕ")
    dec_end = source.index("| _ => 0", dec_start) + len("| _ => 0")
    dec_body = source[dec_start:dec_end]

    def _dec_sub(match: re.Match) -> str:
        panel = int(match.group(1))
        return f"| {panel} => {exponents[panel]}"

    dec_body = re.sub(r"\| (\d+) => \d+", _dec_sub, dec_body)
    source = source[:dec_start] + dec_body + source[dec_end:]

    # Backfill the six chunk-group center replay values (they carried
    # owner-00 literals and evaluated to False).
    for chunk, chunk_total in enumerate(chunk_totals):
        source = replace_replay_value(source, f"chunkCenters_replay2628K04_{chunk}", chunk_total)
    source = replace_replay_value(source, "totalCenters_replay2628K04", total)

    # Re-render probeEpsReplay2628K04 wholesale: the template's left side
    # nested sum carries owner-00 exponents and the owner-00 edge charge.
    eps_block = (
        "theorem probeEpsReplay2628K04 :\n"
        f"    {nested_eps_sum(edge_charge, exponents)}\n"
        f"  = (( {eps.numerator} : ℚ) / {eps.denominator}) := by\n"
        "  norm_num\n"
    )
    source = replace_theorem_block(source, "probeEpsReplay2628K04", eps_block)

    # Drop the owner-00 probeFinal pair (their literals were row-00 relics;
    # the membership proof now consumes probeCloseLo/Hi plus cast bridges).
    for name in ("probeFinalLo2628K04", "probeFinalHi2628K04"):
        start = source.index(f"theorem {name} :")
        next_theorem = source.find("\ntheorem ", start + 1)
        source = source[:start] + source[next_theorem + 1:]

    # The probeCloseLo/Hi template theorems are superseded: the membership
    # proof now uses the Entry000 margin pattern (reLo + eps <= center as a
    # single norm_num with the interval and the sum expanded together).
    for name in ("probeCloseLo2628K04", "probeCloseHi2628K04"):
        start = source.index(f"theorem {name} :")
        next_theorem = source.find("\ntheorem ", start + 1)
        if next_theorem < 0:
            next_theorem = source.index("\nend ConnesWeilRH.Dev")
        source = source[:start] + source[next_theorem + 1:]

    # Big-value norm_num expansions need deep recursion and a large
    # heartbeat budget (ZProbe2628CenterSum / Entry000 convention).
    namespace_start = source.index("namespace ConnesWeilRH.Dev")
    source = (source[:namespace_start]
              + "set_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n\n"
              + source[namespace_start:])

    # The membership proof needs the diagonal phase facts plus the K04
    # edge-charge certificate (not in the owner-00 import closure).
    first_import_end = source.index("\n") + 1
    source = source[:first_import_end] + (
        "import ConnesWeilRH.Dev.C1RouteAAnalyticMomentDiagonal2618\n"
        "import ConnesWeilRH.Dev.C1RouteAMomentActualEdge2620K04\n"
    ) + source[first_import_end:]

    # Chunked center/eps sums: a single 180-term norm_num dies on the
    # heartbeat budget (v5 incident), so each sum goes through six 30-term
    # blocks plus a sum_range_add_sum_Ico assembly (ZProbe2628CenterSum
    # pattern). Each block states its replay LITERAL on the right (the
    # chunk defs branch into imported panel-table constants, which a
    # block-local norm_num cannot evaluate - v10 incident) and unfolds
    # exactly its own 30 panel-table constants.
    centers_blocks = "\n\n".join(
        f"private theorem centersBlock2628K04_{chunk} :\n"
        f"    ∑ p ∈ Finset.Ico {chunk * 30} {chunk * 30 + 30},"
        f" ((partitionCenter2628K04 p : ℚ) : ℝ) =\n"
        f"      (( {chunk_totals[chunk].numerator} : ℚ) /"
        f" {chunk_totals[chunk].denominator}) := by\n"
        f"  rw [Finset.sum_Ico_eq_sum_range]\n"
        f"  norm_num [partitionCenter2628K04,"
        + ",".join(
            f" momentPanelIntegralCenter2622K04P{panel:03d}"
            for panel in range(chunk * 30, (chunk + 1) * 30)
        )
        + ", Finset.sum_range_succ]"
        for chunk in range(6)
    ) + "\n"
    centers_rws = "\n".join(
        f"  rw [← Finset.sum_range_add_sum_Ico"
        f" (f := fun p => ((partitionCenter2628K04 p : ℚ) : ℝ))"
        f" (show {bound} ≤ {bound + 30} by norm_num)]"
        for bound in (150, 120, 90, 60, 30, 0)
    ) + "\n"
    eps_blocks = "\n\n".join(
        f"private theorem epsChunk2628K04_{chunk} :\n"
        f"    ∑ p ∈ Finset.Ico {chunk * 30} {chunk * 30 + 30},"
        f" (1 : ℚ) / 10 ^ dec2628K04 p =\n"
        f"      (( {eps_chunks[chunk].numerator} : ℚ) / {eps_chunks[chunk].denominator}) := by\n"
        f"  rw [Finset.sum_Ico_eq_sum_range]\n"
        f"  norm_num [dec2628K04, Finset.sum_range_succ]"
        for chunk in range(6)
    ) + "\n"
    eps_rws = "\n".join(
        f"  rw [← Finset.sum_range_add_sum_Ico"
        f" (f := fun p => (1 : ℚ) / 10 ^ dec2628K04 p)"
        f" (show {bound} ≤ {bound + 30} by norm_num)]"
        for bound in (150, 120, 90, 60, 30, 0)
    ) + "\n"

    namespace_end = source.rfind("\nend ConnesWeilRH.Dev\n")
    if namespace_end < 0:
        raise RuntimeError("missing namespace terminator")
    appendix = """

/-- Verbatim copy of `analyticMomentInterval2597_row_04` element 5 — the
entry-(4,4) analytic interval. The verbatim token stream is what makes the
kernel-rfl bridge below close: simp/norm_num peeling of the matrix
application stalls at index 4 (record-2634 micro campaign), so the
membership proof goes through this copy instead. -/
noncomputable def entry44Interval2628 : ComplexRect2427 :=
    {entry44}

theorem entry44Interval2628_eq :
    (analyticMomentInterval2597
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))) = entry44Interval2628 := rfl

{centers_blocks}
theorem partitionCentersSum2628K04 :
    ∑ p ∈ Finset.range 180, ((partitionCenter2628K04 p : ℚ) : ℝ) =
      ((totalCenters2628K04 : ℚ) : ℝ) := by
  rw [totalCenters_replay2628K04]
{centers_rws}
  rw [centersBlock2628K04_0, centersBlock2628K04_1, centersBlock2628K04_2,
    centersBlock2628K04_3, centersBlock2628K04_4, centersBlock2628K04_5]
  norm_num

{eps_blocks}
theorem epsTotal2628K04 :
    ({edge_num} : ℚ) / 10 ^ {edge_exp} +
      ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628K04 p =
      (( {eps_num} : ℚ) / {eps_den}) := by
{eps_rws}
  rw [epsChunk2628K04_0, epsChunk2628K04_1, epsChunk2628K04_2,
    epsChunk2628K04_3, epsChunk2628K04_4, epsChunk2628K04_5]
  norm_num

theorem actualFullRealError2628K04 :
    |(storedWidth 4 ^ 2) * (∫ x in (-1 : ℝ)..1,
        realNormalizedMomentIntegrand2618 (storedWidth 4 ^ 2)
          (capturedNodes2584 4).re x) -
      ((totalCenters2628K04 : ℚ) : ℝ)| ≤
      (((({edge_num} : ℚ) / 10 ^ {edge_exp} +
        ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628K04 p : ℚ) : ℚ) : ℝ) := by
  let f : ℝ → ℝ := realNormalizedMomentIntegrand2618 (storedWidth 4 ^ 2)
    (capturedNodes2584 4).re
  have hleft := probeIntervalIntegrable2628 (storedWidth 4 ^ 2)
    (capturedNodes2584 4).re (-1) (-(9 / 10 : ℝ))
  have hmid := probeIntervalIntegrable2628 (storedWidth 4 ^ 2)
    (capturedNodes2584 4).re (-(9 / 10 : ℝ)) (9 / 10)
  have hright := probeIntervalIntegrable2628 (storedWidth 4 ^ 2)
    (capturedNodes2584 4).re (9 / 10) 1
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals hmid hright
  have houter := intervalIntegral.integral_add_adjacent_intervals hleft
    (probeIntervalIntegrable2628 (storedWidth 4 ^ 2)
      (capturedNodes2584 4).re (-(9 / 10 : ℝ)) 1)
  have hedge := actualMomentEntry04_bothEdgeCharge_le2620
  have hcenters := partitionCentersSum2628K04
  have hpanel :
      |(storedWidth 4 ^ 2) * (∫ x in (-(9 / 10 : ℝ))..(9 / 10 : ℝ), f x) -
          ((totalCenters2628K04 : ℚ) : ℝ)| ≤
        ∑ p ∈ Finset.range 180, (1 : ℝ) / 10 ^ dec2628K04 p := by
    have hpanel0 :
        |(storedWidth 4 ^ 2) * (∫ x in (-9 / 10 : ℝ)..(9 / 10 : ℝ),
            realNormalizedMomentIntegrand2618 (storedWidth 4 ^ 2)
              (capturedNodes2584 4).re x) -
            ((totalCenters2628K04 : ℚ) : ℝ)| ≤
          ∑ p ∈ Finset.range 180, (1 : ℝ) / 10 ^ dec2628K04 p := by
      rw [← panelIntegrals2628K04_sum_eq_global, ← hcenters]
      rw [← Finset.sum_sub_distrib]
      exact panelErrorSum2628K04
    convert hpanel0 using 1 <;> norm_num [f]
  have hdecomp :
      (storedWidth 4 ^ 2) * (∫ x in (-1 : ℝ)..1, f x) -
          ((totalCenters2628K04 : ℚ) : ℝ) =
        ((storedWidth 4 ^ 2) *
          ((∫ x in (-1 : ℝ)..(-(9 / 10 : ℝ)), f x) +
            (∫ x in (9 / 10 : ℝ)..1, f x))) +
        ((storedWidth 4 ^ 2) * (∫ x in (-(9 / 10 : ℝ))..(9 / 10 : ℝ), f x) -
          ((totalCenters2628K04 : ℚ) : ℝ)) := by
    dsimp [f] at hsplit2 houter ⊢
    rw [← houter, ← hsplit2]
    ring
  rw [hdecomp]
  calc
    |((storedWidth 4 ^ 2) *
        ((∫ x in (-1 : ℝ)..(-(9 / 10 : ℝ)), f x) +
          (∫ x in (9 / 10 : ℝ)..1, f x))) +
        ((storedWidth 4 ^ 2) * (∫ x in (-(9 / 10 : ℝ))..(9 / 10 : ℝ), f x) -
          ((totalCenters2628K04 : ℚ) : ℝ))| ≤
      |(storedWidth 4 ^ 2) *
        ((∫ x in (-1 : ℝ)..(-(9 / 10 : ℝ)), f x) +
          (∫ x in (9 / 10 : ℝ)..1, f x))| +
        |(storedWidth 4 ^ 2) * (∫ x in (-(9 / 10 : ℝ))..(9 / 10 : ℝ), f x) -
          ((totalCenters2628K04 : ℚ) : ℝ)| := abs_add_le _ _
    _ ≤ (({edge_num} : ℝ) / 10 ^ {edge_exp}) +
           ∑ p ∈ Finset.range 180, (1 : ℝ) / 10 ^ dec2628K04 p := by
      exact add_le_add hedge hpanel
    _ = (((({edge_num} : ℚ) / 10 ^ {edge_exp} +
        ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628K04 p : ℚ) : ℚ) : ℝ) := by
      norm_num

theorem marginLo2628K04 :
    (analyticMomentInterval2597 4 4).reLo +
        ((({edge_num} : ℚ) / 10 ^ {edge_exp} +
          ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628K04 p : ℚ) : ℚ) ≤
      ((totalCenters2628K04 : ℚ) : ℝ) := by
  have hsucc04 : (analyticMomentInterval2597 4 4) =
      (analyticMomentInterval2597
        (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
        (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))) := rfl
  have hreLo : (analyticMomentInterval2597
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))).reLo =
      {relo_field} := rfl
  rw [hsucc04, hreLo, totalCenters_replay2628K04, epsTotal2628K04]
  norm_num

theorem marginHi2628K04 :
    ((totalCenters2628K04 : ℚ) : ℝ) +
        ((({edge_num} : ℚ) / 10 ^ {edge_exp} +
          ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628K04 p : ℚ) : ℚ) ≤
      (analyticMomentInterval2597 4 4).reHi := by
  have hsucc04 : (analyticMomentInterval2597 4 4) =
      (analyticMomentInterval2597
        (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
        (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))) := rfl
  have hreHi : (analyticMomentInterval2597
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))).reHi =
      {rehi_field} := rfl
  rw [hsucc04, hreHi, totalCenters_replay2628K04, epsTotal2628K04]
  norm_num

theorem entry04_imLo_nonpos2628K04 :
    (analyticMomentInterval2597 4 4).imLo ≤ 0 := by
  have hsucc04 : (analyticMomentInterval2597 4 4) =
      (analyticMomentInterval2597
        (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
        (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))) := rfl
  have himLo : (analyticMomentInterval2597
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))).imLo =
      {imlo_field} := rfl
  rw [hsucc04, himLo]
  norm_num

theorem entry04_imHi_nonneg2628K04 :
    0 ≤ (analyticMomentInterval2597 4 4).imHi := by
  have hsucc04 : (analyticMomentInterval2597 4 4) =
      (analyticMomentInterval2597
        (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
        (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))) := rfl
  have himHi : (analyticMomentInterval2597
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))).imHi =
      {imhi_field} := rfl
  rw [hsucc04, himHi]
  norm_num

theorem actualOwnerMomentMatrix2351_entry04_mem2628 :
    (analyticMomentInterval2597 4 4).Mem
      (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 4 4) := by
  have hphase := capturedDiagonalPhase2618 4
  have hentry := momentEntry2351_eq_realIntegral_of_phase_cancel2618
    capturedModulations2584 4 (capturedNodes2584 4) hphase
  have herr := actualFullRealError2628K04
  have herrlo := (abs_le.mp herr).1
  have herrhi := (abs_le.mp herr).2
  have hmarginLo := marginLo2628K04
  have hmarginHi := marginHi2628K04
  change (analyticMomentInterval2597 4 4).Mem
    (momentEntry2351 capturedModulations2584 4 (capturedNodes2584 4))
  rw [hentry]
  change (analyticMomentInterval2597 4 4).reLo ≤
      storedWidth 4 ^ 2 * (∫ coordinate in (-1 : ℝ)..1,
        realNormalizedMomentIntegrand2618 (storedWidth 4 ^ 2)
          (capturedNodes2584 4).re coordinate) ∧
    storedWidth 4 ^ 2 * (∫ coordinate in (-1 : ℝ)..1,
        realNormalizedMomentIntegrand2618 (storedWidth 4 ^ 2)
          (capturedNodes2584 4).re coordinate) ≤
      (analyticMomentInterval2597 4 4).reHi ∧
    (analyticMomentInterval2597 4 4).imLo ≤ 0 ∧
    0 ≤ (analyticMomentInterval2597 4 4).imHi
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · exact entry04_imLo_nonpos2628K04
  · exact entry04_imHi_nonneg2628K04

end ConnesWeilRH.Dev
""".format(
        edge_num=edge_charge[0],
        edge_exp=edge_charge[1],
        entry44=entry44_text,
        relo_field=entry44_fields["reLo"],
        rehi_field=entry44_fields["reHi"],
        imlo_field=entry44_fields["imLo"],
        imhi_field=entry44_fields["imHi"],
        centers_blocks=centers_blocks,
        centers_rws=centers_rws,
        eps_blocks=eps_blocks,
        eps_rws=eps_rws,
        eps_num=eps.numerator,
        eps_den=eps.denominator,
    )
    source = source[:namespace_end] + appendix
    target = DEV / "ZProbe2628K04.lean"
    target.write_text(source, encoding="utf-8", newline="\n")
    print(target)
    print(f"total={total} eps={eps} lo={lo_q} hi={hi_q} edge={edge_charge}")


if __name__ == "__main__":
    main()
