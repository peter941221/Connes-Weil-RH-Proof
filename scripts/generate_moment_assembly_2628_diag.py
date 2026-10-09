"""Regenerate a diagonal-owner moment-assembly probe (record 2634 generalized).

Generalizes scripts/generate_moment_assembly_2628_k04.py (record 2634,
owner 4) to any diagonal owner index: --owner-index D emits
ZProbe2628K{D:02d}.lean certifying that the 2597 entry-(D, D) analytic
interval contains the owner moment integral, with every numeric fact
re-derived from the owner's own sources:

- per-panel centers from the owner's K{D:02d} panel tables,
- per-panel error exponents from the owner's actual-panel certificates,
- the edge charge from the owner's edge certificate (owner 0 reads the
  committed pre-rename module `C1RouteAMomentActualEdge2620` whose
  theorem carries the three-zero name `actualMomentEntry000_...`;
  owners >= 1 read the K{D:02d}-suffixed module, which must exist
  before this runs),
- the entry-(D, D) element verbatim from the 2597 module (AGENTS 2cc:
  verbatim copy + kernel rfl; norm_num never unfolds the emitted def).

Owner 0 peels the 2597 matrix at the head (numeral indices, the record
2618 Diagonal2618 precedent), so no succ bridge is emitted; owners >= 1
go through the Fin.succ chain first (the record-2634 owner-4 shape).

The K04 module stays untouched; the d = 4 output of this script is
equivalent to it by construction but NOT byte-identical (edge module
provenance differs), so record 2634's committed bytes remain the
certificate of reference for owner 4.
"""
import argparse
import re
import sys
from fractions import Fraction
from pathlib import Path

sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH" / "Dev"


def edge_theorem_name(owner: int) -> str:
    """Owner 0 predates the K-suffix rename: its committed edge theorem
    keeps the original three-zero label (2620 generator)."""
    if owner == 0:
        return "actualMomentEntry000_bothEdgeCharge_le2620"
    return f"actualMomentEntry{owner:02d}_bothEdgeCharge_le2620"


def edge_module_name(owner: int) -> str:
    if owner == 0:
        return "C1RouteAMomentActualEdge2620"
    return f"C1RouteAMomentActualEdge2620K{owner:02d}"


def read_owner_panel_data(owner: int):
    suffix = f"K{owner:02d}"
    centers = []
    exponents = []
    for panel in range(180):
        table = (DEV / f"C1RouteAMomentPanelTable2622{suffix}Panel{panel:03d}.lean").read_text(encoding="utf-8")
        center_match = re.search(
            rf"def momentPanelIntegralCenter2622{suffix}P{panel:03d} : .*? := \(\((\d+) .*? / (\d+)",
            table)
        if center_match is None:
            raise RuntimeError(f"missing owner-{owner:02d} center for panel {panel}")
        centers.append(Fraction(int(center_match[1]), int(center_match[2])))
        actual = (DEV / f"C1RouteAMomentActualPanel2622{suffix}Panel{panel:03d}.lean").read_text(encoding="utf-8")
        exponent_match = re.search(
            rf"actualMomentPanel{suffix}{panel:03d}_integral_error_le2622[\s\S]*?/ 10 \^ (\d+)",
            actual)
        if exponent_match is None:
            raise RuntimeError(f"missing owner-{owner:02d} error exponent for panel {panel}")
        exponents.append(int(exponent_match[1]))
    edge_source = (DEV / f"{edge_module_name(owner)}.lean").read_text(encoding="utf-8")
    edge_match = re.search(
        rf"{edge_theorem_name(owner)}[\s\S]*?\(\s*(\d+)\s*:\s*ℝ\s*\)\s*/\s*10 \^ (\d+)",
        edge_source)
    if edge_match is None:
        raise RuntimeError(f"missing owner-{owner:02d} edge charge")
    edge_charge = (int(edge_match.group(1)), int(edge_match.group(2)))
    return centers, exponents, edge_charge


def read_diag_element(owner: int) -> dict:
    """Row_{owner} element (owner + 1) verbatim from the 2597 source.

    Same law as record 2634: the def body must be the SAME literal term
    the 2597 module elaborated, and continuation lines must keep their
    original deep indentation (a field token at the opening-brace column
    makes the structure parser close the literal after field 1).
    """
    src = (DEV / "C1RouteACorrectionAnalyticIntervals2597.lean").read_text(encoding="utf-8")
    match = re.search(
        rf"noncomputable def analyticMomentInterval2597_row_{owner:02d} : Fin 30 → ComplexRect2427 :=\s*\n\s*!\[(.*?)\]\s*$",
        src, re.S | re.M)
    if match is None:
        raise RuntimeError(f"missing row_{owner:02d} matrix literal")
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
        raise RuntimeError(f"row_{owner:02d} parse found {len(elems)} elements, expected 30")
    element = elems[owner].strip()
    lines = element.splitlines()
    fields = {}
    for i, name in enumerate(("reLo", "reHi", "imLo", "imHi")):
        field_match = re.search(re.escape(name) + r" := (.+?)(,?)$", lines[i].strip())
        if field_match is None:
            raise RuntimeError(f"missing field {name} in row_{owner:02d} element {owner + 1}")
        # the imHi line ends with the element's closing brace; a field
        # value itself never ends with ',' or '}' (numerals, parens, /)
        fields[name] = field_match.group(1).rstrip(",}")
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


def drop_theorem(source: str, name: str) -> str:
    start = source.index(f"theorem {name} :")
    next_theorem = source.find("\ntheorem ", start + 1)
    if next_theorem < 0:
        next_theorem = source.index("\nend ConnesWeilRH.Dev")
    return source[:start] + source[next_theorem + 1:]


def replace_replay_value(source: str, theorem_name: str, value: Fraction) -> str:
    """Replace the decimal-fraction right-hand side of a replay theorem."""
    pattern = rf"(theorem {theorem_name} :[^=]+=)\s*\(\((\d+) : ℚ\) / (\d+)\)"
    replacement = rf"\g<1> (( {value.numerator} : ℚ) / {value.denominator})"
    new_source, count = re.subn(pattern, replacement, source, count=1)
    if count != 1:
        raise RuntimeError(f"cannot rewrite replay value of {theorem_name}")
    return new_source


def succ_chain_text(owner: int) -> str:
    """The index spelling for kernel-rfl bridges. Owner 0 peels at the
    matrix head with numeral indices (record 2618 Diagonal2618); owners
    >= 1 need the Fin.succ chain (record 2634 owner-4 micro campaign)."""
    if owner == 0:
        return "0"
    return "(" + " (Fin.succ " * owner + "0" + ")" * owner + ")"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--owner-index", type=int, required=True, choices=range(30))
    arguments = parser.parse_args()
    owner = arguments.owner_index
    suffix = f"K{owner:02d}"
    if owner == 4:
        raise SystemExit("owner 4 is record 2634's committed module; use the K04 script")

    centers, exponents, edge_charge = read_owner_panel_data(owner)
    entry = read_diag_element(owner)
    edge_theorem = edge_theorem_name(owner)
    edge_fraction = Fraction(edge_charge[0], 10 ** edge_charge[1])
    total = sum(centers, Fraction())
    eps = edge_fraction + sum((Fraction(1, 10 ** exponent) for exponent in exponents), Fraction())
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

    chain_text = succ_chain_text(owner)
    if owner == 0:
        hsucc_have = ""
        succ_rw = ""
    else:
        hsucc_have = (
            "  have hsucc : (analyticMomentInterval2597 %d %d) =\n"
            "      (analyticMomentInterval2597 %s %s) := rfl\n"
            % (owner, owner, chain_text, chain_text)
        )
        succ_rw = "hsucc, "

    source = (DEV / "ZProbe2628Sum.lean").read_text(encoding="utf-8")
    source = re.sub(r"C1RouteAMomentActualPanel2622Panel([0-9]{3})",
                    rf"C1RouteAMomentActualPanel2622{suffix}Panel\1", source)
    source = re.sub(r"actualMomentPanel([0-9]{3})_integral_error_le2622",
                    rf"actualMomentPanel{suffix}\1_integral_error_le2622", source)
    replacements = {
        "momentPanelIntegralCenter2622P": f"momentPanelIntegralCenter2622{suffix}P",
        "storedWidth 0": f"storedWidth {owner}",
        "capturedNodes2584 0": f"capturedNodes2584 {owner}",
        "analyticMomentInterval2597 0 0": f"analyticMomentInterval2597 {owner} {owner}",
        "analyticMomentInterval2597_row_00": f"analyticMomentInterval2597_row_{owner:02d}",
        "partitionCenter2628": f"partitionCenter2628{suffix}",
        "chunkCenters_replay2628": f"chunkCenters_replay2628{suffix}",
        "chunkCenters2628": f"chunkCenters2628{suffix}",
        "dec2628": f"dec2628{suffix}",
        "panelIntegral2628": f"panelIntegral2628{suffix}",
        "panelError2628": f"panelError2628{suffix}",
        "totalCenters2628": f"totalCenters2628{suffix}",
        "panelIntegrals2628_sum_eq_global": f"panelIntegrals2628{suffix}_sum_eq_global",
        "panelErrorSum2628": f"panelErrorSum2628{suffix}",
        "totalCenters_replay2628": f"totalCenters_replay2628{suffix}",
        "probeEpsReplay2628": f"probeEpsReplay2628{suffix}",
        "probeFinalLo2628": f"probeFinalLo2628{suffix}",
        "probeFinalHi2628": f"probeFinalHi2628{suffix}",
        "probeCloseLo2628": f"probeCloseLo2628{suffix}",
        "probeCloseHi2628": f"probeCloseHi2628{suffix}",
    }
    for old, new in replacements.items():
        source = source.replace(old, new)

    # Backfill the per-panel exponent branches: the template's dec branches
    # carry the original owner-00 exponents, which need not match the
    # regenerated K{D:02d} panel certificates (record-2634 incident:
    # strictly tighter bounds broke panelError at a type mismatch).
    dec_start = source.index(f"def dec2628{suffix} : ℕ → ℕ")
    dec_end = source.index("| _ => 0", dec_start) + len("| _ => 0")
    dec_body = source[dec_start:dec_end]

    def _dec_sub(match: re.Match) -> str:
        panel = int(match.group(1))
        return f"| {panel} => {exponents[panel]}"

    dec_body = re.sub(r"\| (\d+) => \d+", _dec_sub, dec_body)
    source = source[:dec_start] + dec_body + source[dec_end:]

    # Backfill the six chunk-group center replay values (they carried the
    # template's literals and would evaluate to False).
    for chunk, chunk_total in enumerate(chunk_totals):
        source = replace_replay_value(source, f"chunkCenters_replay2628{suffix}_{chunk}", chunk_total)
    source = replace_replay_value(source, f"totalCenters_replay2628{suffix}", total)

    # Re-render probeEpsReplay wholesale: the template's left side nested
    # sum carries template exponents and the template edge charge.
    eps_block = (
        f"theorem probeEpsReplay2628{suffix} :\n"
        f"    {nested_eps_sum(edge_charge, exponents)}\n"
        f"  = (( {eps.numerator} : ℚ) / {eps.denominator}) := by\n"
        "  norm_num\n"
    )
    source = replace_theorem_block(source, f"probeEpsReplay2628{suffix}", eps_block)

    # Drop the template's probeFinal pair and probeClose pair (their
    # literals are owner-00 relics; the membership proof consumes the
    # module-level margins plus the cast bridges instead).
    for name in (f"probeFinalLo2628{suffix}", f"probeFinalHi2628{suffix}",
                 f"probeCloseLo2628{suffix}", f"probeCloseHi2628{suffix}"):
        source = drop_theorem(source, name)

    # Big-value norm_num expansions need deep recursion and a large
    # heartbeat budget (ZProbe2628CenterSum / Entry000 convention).
    namespace_start = source.index("namespace ConnesWeilRH.Dev")
    source = (source[:namespace_start]
              + "set_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n\n"
              + source[namespace_start:])

    # The membership proof needs the diagonal phase facts plus the owner's
    # edge-charge certificate (not in the template's import closure).
    first_import_end = source.index("\n") + 1
    source = source[:first_import_end] + (
        "import ConnesWeilRH.Dev.C1RouteAAnalyticMomentDiagonal2618\n"
        f"import ConnesWeilRH.Dev.{edge_module_name(owner)}\n"
    ) + source[first_import_end:]

    # Chunked center/eps sums: a single 180-term norm_num dies on the
    # heartbeat budget (v5 incident), so each sum goes through six 30-term
    # blocks plus a sum_range_add_sum_Ico assembly (ZProbe2628CenterSum
    # pattern). Each block states its replay LITERAL on the right (the
    # chunk defs branch into imported panel-table constants, which a
    # block-local norm_num cannot evaluate - v10 incident) and unfolds
    # exactly its own 30 panel-table constants. (For owner 0 the renamed
    # partitionCenter branches hold numerals directly, so the named
    # table constants are simply unused simp args - harmless.)
    centers_blocks = "\n\n".join(
        f"private theorem centersBlock2628{suffix}_{chunk} :\n"
        f"    ∑ p ∈ Finset.Ico {chunk * 30} {chunk * 30 + 30},"
        f" ((partitionCenter2628{suffix} p : ℚ) : ℝ) =\n"
        f"      (( {chunk_totals[chunk].numerator} : ℚ) /"
        f" {chunk_totals[chunk].denominator}) := by\n"
        f"  rw [Finset.sum_Ico_eq_sum_range]\n"
        f"  norm_num [partitionCenter2628{suffix},"
        + ",".join(
            f" momentPanelIntegralCenter2622{suffix}P{panel:03d}"
            for panel in range(chunk * 30, (chunk + 1) * 30)
        )
        + ", Finset.sum_range_succ]"
        for chunk in range(6)
    ) + "\n"
    centers_rws = "\n".join(
        f"  rw [← Finset.sum_range_add_sum_Ico"
        f" (f := fun p => ((partitionCenter2628{suffix} p : ℚ) : ℝ))"
        f" (show {bound} ≤ {bound + 30} by norm_num)]"
        for bound in (150, 120, 90, 60, 30, 0)
    ) + "\n"
    eps_blocks = "\n\n".join(
        f"private theorem epsChunk2628{suffix}_{chunk} :\n"
        f"    ∑ p ∈ Finset.Ico {chunk * 30} {chunk * 30 + 30},"
        f" (1 : ℚ) / 10 ^ dec2628{suffix} p =\n"
        f"      (( {eps_chunks[chunk].numerator} : ℚ) / {eps_chunks[chunk].denominator}) := by\n"
        f"  rw [Finset.sum_Ico_eq_sum_range]\n"
        f"  norm_num [dec2628{suffix}, Finset.sum_range_succ]"
        for chunk in range(6)
    ) + "\n"
    eps_rws = "\n".join(
        f"  rw [← Finset.sum_range_add_sum_Ico"
        f" (f := fun p => (1 : ℚ) / 10 ^ dec2628{suffix} p)"
        f" (show {bound} ≤ {bound + 30} by norm_num)]"
        for bound in (150, 120, 90, 60, 30, 0)
    ) + "\n"

    namespace_end = source.rfind("\nend ConnesWeilRH.Dev\n")
    if namespace_end < 0:
        raise RuntimeError("missing namespace terminator")
    appendix = """

/-- Verbatim copy of `analyticMomentInterval2597_row_{row:02d}` element
{elem:2d} — the entry-({owner}, {owner}) analytic interval. The verbatim
token stream is what makes the kernel-rfl bridge below close:
simp/norm_num peeling of the matrix application stalls at nonzero
indices (record-2634 micro campaign), so every numeric consumer goes
through per-field rfl bridges against this copy instead. -/
noncomputable def entry{dd}Interval2628 : ComplexRect2427 :=
    {entry44}

theorem entry{dd}Interval2628_eq :
    (analyticMomentInterval2597
      {chain}
      {chain}) = entry{dd}Interval2628 := rfl

{centers_blocks}
theorem partitionCentersSum2628{S} :
    ∑ p ∈ Finset.range 180, ((partitionCenter2628{S} p : ℚ) : ℝ) =
      ((totalCenters2628{S} : ℚ) : ℝ) := by
  rw [totalCenters_replay2628{S}]
{centers_rws}
  rw [centersBlock2628{S}_0, centersBlock2628{S}_1, centersBlock2628{S}_2,
    centersBlock2628{S}_3, centersBlock2628{S}_4, centersBlock2628{S}_5]
  norm_num

{eps_blocks}
theorem epsTotal2628{S} :
    ({edge_num} : ℚ) / 10 ^ {edge_exp} +
      ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628{S} p =
      (( {eps_num} : ℚ) / {eps_den}) := by
{eps_rws}
  rw [epsChunk2628{S}_0, epsChunk2628{S}_1, epsChunk2628{S}_2,
    epsChunk2628{S}_3, epsChunk2628{S}_4, epsChunk2628{S}_5]
  norm_num

theorem actualFullRealError2628{S} :
    |(storedWidth {owner} ^ 2) * (∫ x in (-1 : ℝ)..1,
        realNormalizedMomentIntegrand2618 (storedWidth {owner} ^ 2)
          (capturedNodes2584 {owner}).re x) -
      ((totalCenters2628{S} : ℚ) : ℝ)| ≤
      (((({edge_num} : ℚ) / 10 ^ {edge_exp} +
        ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628{S} p : ℚ) : ℚ) : ℝ) := by
  let f : ℝ → ℝ := realNormalizedMomentIntegrand2618 (storedWidth {owner} ^ 2)
    (capturedNodes2584 {owner}).re
  have hleft := probeIntervalIntegrable2628 (storedWidth {owner} ^ 2)
    (capturedNodes2584 {owner}).re (-1) (-(9 / 10 : ℝ))
  have hmid := probeIntervalIntegrable2628 (storedWidth {owner} ^ 2)
    (capturedNodes2584 {owner}).re (-(9 / 10 : ℝ)) (9 / 10)
  have hright := probeIntervalIntegrable2628 (storedWidth {owner} ^ 2)
    (capturedNodes2584 {owner}).re (9 / 10) 1
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals hmid hright
  have houter := intervalIntegral.integral_add_adjacent_intervals hleft
    (probeIntervalIntegrable2628 (storedWidth {owner} ^ 2)
      (capturedNodes2584 {owner}).re (-(9 / 10 : ℝ)) 1)
  have hedge := {edge_theorem}
  have hcenters := partitionCentersSum2628{S}
  have hpanel :
      |(storedWidth {owner} ^ 2) * (∫ x in (-(9 / 10 : ℝ))..(9 / 10 : ℝ), f x) -
          ((totalCenters2628{S} : ℚ) : ℝ)| ≤
        ∑ p ∈ Finset.range 180, (1 : ℝ) / 10 ^ dec2628{S} p := by
    have hpanel0 :
        |(storedWidth {owner} ^ 2) * (∫ x in (-9 / 10 : ℝ)..(9 / 10 : ℝ),
            realNormalizedMomentIntegrand2618 (storedWidth {owner} ^ 2)
              (capturedNodes2584 {owner}).re x) -
            ((totalCenters2628{S} : ℚ) : ℝ)| ≤
          ∑ p ∈ Finset.range 180, (1 : ℝ) / 10 ^ dec2628{S} p := by
      rw [← panelIntegrals2628{S}_sum_eq_global, ← hcenters]
      rw [← Finset.sum_sub_distrib]
      exact panelErrorSum2628{S}
    convert hpanel0 using 1 <;> norm_num [f]
  have hdecomp :
      (storedWidth {owner} ^ 2) * (∫ x in (-1 : ℝ)..1, f x) -
          ((totalCenters2628{S} : ℚ) : ℝ) =
        ((storedWidth {owner} ^ 2) *
          ((∫ x in (-1 : ℝ)..(-(9 / 10 : ℝ)), f x) +
            (∫ x in (9 / 10 : ℝ)..1, f x))) +
        ((storedWidth {owner} ^ 2) * (∫ x in (-(9 / 10 : ℝ))..(9 / 10 : ℝ), f x) -
          ((totalCenters2628{S} : ℚ) : ℝ)) := by
    dsimp [f] at hsplit2 houter ⊢
    rw [← houter, ← hsplit2]
    ring
  rw [hdecomp]
  calc
    |((storedWidth {owner} ^ 2) *
        ((∫ x in (-1 : ℝ)..(-(9 / 10 : ℝ)), f x) +
          (∫ x in (9 / 10 : ℝ)..1, f x))) +
        ((storedWidth {owner} ^ 2) * (∫ x in (-(9 / 10 : ℝ))..(9 / 10 : ℝ), f x) -
          ((totalCenters2628{S} : ℚ) : ℝ))| ≤
      |(storedWidth {owner} ^ 2) *
        ((∫ x in (-1 : ℝ)..(-(9 / 10 : ℝ)), f x) +
          (∫ x in (9 / 10 : ℝ)..1, f x))| +
        |(storedWidth {owner} ^ 2) * (∫ x in (-(9 / 10 : ℝ))..(9 / 10 : ℝ), f x) -
          ((totalCenters2628{S} : ℚ) : ℝ)| := abs_add_le _ _
    _ ≤ (({edge_num} : ℝ) / 10 ^ {edge_exp}) +
           ∑ p ∈ Finset.range 180, (1 : ℝ) / 10 ^ dec2628{S} p := by
      exact add_le_add hedge hpanel
    _ = (((({edge_num} : ℚ) / 10 ^ {edge_exp} +
        ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628{S} p : ℚ) : ℚ) : ℝ) := by
      norm_num

theorem marginLo2628{S} :
    (analyticMomentInterval2597 {owner} {owner}).reLo +
        (((({edge_num} : ℚ) / 10 ^ {edge_exp} +
          ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628{S} p : ℚ) : ℚ) : ℚ) ≤
      ((totalCenters2628{S} : ℚ) : ℝ) := by
{hsucc_have}  have hreLo : (analyticMomentInterval2597
      {chain}
      {chain}).reLo =
      {relo_field} := rfl
  rw [{succ_rw}hreLo, totalCenters_replay2628{S}, epsTotal2628{S}]
  norm_num

theorem marginHi2628{S} :
    ((totalCenters2628{S} : ℚ) : ℝ) +
        (((({edge_num} : ℚ) / 10 ^ {edge_exp} +
          ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628{S} p : ℚ) : ℚ) : ℚ) ≤
      (analyticMomentInterval2597 {owner} {owner}).reHi := by
{hsucc_have}  have hreHi : (analyticMomentInterval2597
      {chain}
      {chain}).reHi =
      {rehi_field} := rfl
  rw [{succ_rw}hreHi, totalCenters_replay2628{S}, epsTotal2628{S}]
  norm_num

theorem entry{dd}_imLo_nonpos2628{S} :
    (analyticMomentInterval2597 {owner} {owner}).imLo ≤ 0 := by
{hsucc_have}  have himLo : (analyticMomentInterval2597
      {chain}
      {chain}).imLo =
      {imlo_field} := rfl
  rw [{succ_rw}himLo]
  norm_num

theorem entry{dd}_imHi_nonneg2628{S} :
    0 ≤ (analyticMomentInterval2597 {owner} {owner}).imHi := by
{hsucc_have}  have himHi : (analyticMomentInterval2597
      {chain}
      {chain}).imHi =
      {imhi_field} := rfl
  rw [{succ_rw}himHi]
  norm_num

theorem actualOwnerMomentMatrix2351_entry{dd}_mem2628 :
    (analyticMomentInterval2597 {owner} {owner}).Mem
      (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 {owner} {owner}) := by
  have hphase := capturedDiagonalPhase2618 {owner}
  have hentry := momentEntry2351_eq_realIntegral_of_phase_cancel2618
    capturedModulations2584 {owner} (capturedNodes2584 {owner}) hphase
  have herr := actualFullRealError2628{S}
  have herrlo := (abs_le.mp herr).1
  have herrhi := (abs_le.mp herr).2
  have hmarginLo := marginLo2628{S}
  have hmarginHi := marginHi2628{S}
  change (analyticMomentInterval2597 {owner} {owner}).Mem
    (momentEntry2351 capturedModulations2584 {owner} (capturedNodes2584 {owner}))
  rw [hentry]
  change (analyticMomentInterval2597 {owner} {owner}).reLo ≤
      storedWidth {owner} ^ 2 * (∫ coordinate in (-1 : ℝ)..1,
        realNormalizedMomentIntegrand2618 (storedWidth {owner} ^ 2)
          (capturedNodes2584 {owner}).re coordinate) ∧
    storedWidth {owner} ^ 2 * (∫ coordinate in (-1 : ℝ)..1,
        realNormalizedMomentIntegrand2618 (storedWidth {owner} ^ 2)
          (capturedNodes2584 {owner}).re coordinate) ≤
      (analyticMomentInterval2597 {owner} {owner}).reHi ∧
    (analyticMomentInterval2597 {owner} {owner}).imLo ≤ 0 ∧
    0 ≤ (analyticMomentInterval2597 {owner} {owner}).imHi
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · exact entry{dd}_imLo_nonpos2628{S}
  · exact entry{dd}_imHi_nonneg2628{S}

end ConnesWeilRH.Dev
""".format(
        row=owner,
        elem=owner + 1,
        owner=owner,
        dd=f"{owner:02d}",
        S=suffix,
        chain=chain_text,
        succ_rw=succ_rw,
        hsucc_have=hsucc_have,
        entry44=entry["element"],
        relo_field=entry["fields"]["reLo"],
        rehi_field=entry["fields"]["reHi"],
        imlo_field=entry["fields"]["imLo"],
        imhi_field=entry["fields"]["imHi"],
        edge_theorem=edge_theorem,
        edge_num=edge_charge[0],
        edge_exp=edge_charge[1],
        centers_blocks=centers_blocks,
        centers_rws=centers_rws,
        eps_blocks=eps_blocks,
        eps_rws=eps_rws,
        eps_num=eps.numerator,
        eps_den=eps.denominator,
    )
    source = source[:namespace_end] + appendix
    target = DEV / f"ZProbe2628{suffix}.lean"
    target.write_text(source, encoding="utf-8", newline="\n")
    print(target)
    print(f"total={total} eps={eps} edge={edge_charge}")


if __name__ == "__main__":
    main()
