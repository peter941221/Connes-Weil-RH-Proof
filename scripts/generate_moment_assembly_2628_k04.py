import re
import sys
from fractions import Fraction
from pathlib import Path

sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parent
DEV = ROOT / "ConnesWeilRH" / "Dev"


def main():
    source = (DEV / "ZProbe2628Sum.lean").read_text(encoding="utf-8")
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

    total = sum(centers, Fraction())
    error = Fraction(2, 10**68) + sum((Fraction(1, 10**exponent) for exponent in exponents), Fraction())
    source = re.sub(r"C1RouteAMomentActualPanel2622Panel([0-9]{3})", r"C1RouteAMomentActualPanel2622K04Panel\1", source)
    source = re.sub(r"actualMomentPanel([0-9]{3})_integral_error_le2622", r"actualMomentPanelK04\1_integral_error_le2622", source)
    replacements = {
        "momentPanelIntegralCenter2622P": "momentPanelIntegralCenter2622K04P",
        "storedWidth 0": "storedWidth 4",
        "capturedNodes2584 0": "capturedNodes2584 4",
        "analyticMomentInterval2597 0 0": "analyticMomentInterval2597 4 4",
        "analyticMomentInterval2597_row_00": "analyticMomentInterval2597_row_44",
        "actualMomentEntry000_bothEdgeCharge_le2620": "actualMomentEntry04_bothEdgeCharge_le2620",
        "partitionCenter2628": "partitionCenter2628K04",
        "dec2628": "dec2628K04",
        "panelIntegral2628": "panelIntegral2628K04",
        "panelError2628": "panelError2628K04",
        "totalCenters2628": "totalCenters2628K04",
        "probeFinalLo2628": "probeFinalLo2628K04",
        "probeFinalHi2628": "probeFinalHi2628K04",
        "probeCloseLo2628": "probeCloseLo2628K04",
        "probeCloseHi2628": "probeCloseHi2628K04",
        "panelIntegrals2628_sum_eq_global": "panelIntegrals2628K04_sum_eq_global",
        "panelErrorSum2628": "panelErrorSum2628K04",
        "totalCenters_replay2628": "totalCenters_replay2628K04",
        "probeEpsReplay2628": "probeEpsReplay2628K04",
        "actualFullRealError2628": "actualFullRealError2628K04",
    }
    for old, new in replacements.items():
        source = source.replace(old, new)

    def replace_replay(pattern, value):
        nonlocal source
        match = re.search(pattern, source)
        if match is None:
            raise RuntimeError(f"missing replay matching {pattern}")
        source = re.sub(rf"\\(\\({match[1]}\\s*:\\s*[^)]*\\)\\s*/\\s*{match[2]}\\)", f"(({value.numerator} : {chr(0x211a)}) / {value.denominator})", source, count=1)

    replace_replay(r"theorem totalCenters_replay2628K04 : totalCenters2628K04 = \(\((\d+).*?/ (\d+)\)", total)
    replace_replay(r"theorem probeEpsReplay2628K04 :[\s\S]*?= \(\((\d+).*?/ (\d+)\)", error)
    namespace_end = source.rfind("\nend ConnesWeilRH.Dev\n")
    if namespace_end < 0:
        raise RuntimeError("missing namespace terminator")
    source = source[:namespace_end] + """

theorem actualOwnerMomentMatrix2351_entry04_mem2628 :
    (analyticMomentInterval2597 4 4).Mem
      (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 4 4) := by
  have hentry := momentEntry2351_eq_realIntegral_of_phase_cancel2618
    capturedModulations2584 4 (capturedNodes2584 4) (capturedDiagonalPhase2618 4)
  have herr := actualFullRealError2628K04
  have hlo := (abs_le.mp herr).1
  have hhi := (abs_le.mp herr).2
  change (analyticMomentInterval2597 4 4).Mem
    (momentEntry2351 capturedModulations2584 4 (capturedNodes2584 4))
  rw [hentry]
  have him := actualOwnerMomentMatrix2351_diagonal_im_eq_zero2618 4
  change (analyticMomentInterval2597 4 4).reLo ≤ _ ∧ _ ≤
      (analyticMomentInterval2597 4 4).reHi ∧ _ ≤ 0 ∧ 0 ≤ _
  constructor
  · linarith [probeFinalLo2628K04]
  constructor
  · linarith [probeFinalHi2628K04]
  constructor <;> rw [him] <;>
    norm_num [analyticMomentInterval2597, analyticMomentInterval2597_row_44]

end ConnesWeilRH.Dev
"""
    target = DEV / "ZProbe2628K04.lean"
    target.write_text(source, encoding="utf-8", newline="\n")
    print(target)


if __name__ == "__main__":
    main()
