"""Generate repaired-owner correction-D2 bridges for cell 4096."""

from __future__ import annotations

import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = ROOT / "ConnesWeilRH/Dev/C1RouteARepairedOwnerBaseD22681.lean"
OUT = ROOT / "ConnesWeilRH/Dev"


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def get_factor_boxes() -> list[list[int]]:
    generator = load(
        "base_d2_2682", ROOT / "scripts/generate_routea_repaired_owner_base_d2_2682.py"
    )
    return generator.get_factor_boxes()


def render_family(template: str, family: int, factor: list[int], sign: str) -> str:
    generator = load(
        "base_d2_2682_render", ROOT / "scripts/generate_routea_repaired_owner_base_d2_2682.py"
    )
    source = generator.render(template, family, factor, sign)
    source = source.replace(
        "import ConnesWeilRH.Dev.C1RouteARepairedOwnerCell2678",
        "import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionM02680",
    )
    source = source.replace("record2676BaseD2FamilyRects", "record2676CorrectionD2FamilyRects")
    source = source.replace("record2678BaseCoefficient", "record2680CorrectionCoefficient")
    source = source.replace("record2681", "record2683")
    source = source.replace("BaseD2", "CorrectionD2")
    source = source.replace("Record 2681", "Record 2683")
    return source


def render_consumer() -> str:
    imports = "\n".join(
        f"import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Family{i}"
        for i in range(30)
    )
    cases = "\n".join(
        f"  · exact record2683Family{i}CorrectionD2CellRectMem hx"
        for i in range(30)
    )
    return f"""{imports}

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/- Record 2683: all repaired-owner correction-D2 family bridges feed the
   existing correction-D2 cell consumer. -/

theorem record2683RepairedOwnerCorrectionD2CellContained {{position : ℝ}}
    (hposition : position ∈ Set.Icc 0 record2675CellRight) :
    record2675CorrectionD2Rect.Mem
      (deriv (deriv (correctedPhysical record2680CorrectionCoefficient
        capturedModulations2584)) position) := by
  apply correction_D2CellSumContained
  intro index x hx
  fin_cases index
{cases}
  exact hposition

end ConnesWeilRH.Dev
"""


def main() -> None:
    template = TEMPLATE.read_text(encoding="utf-8")
    factors = get_factor_boxes()
    positive, zero = {2, 3}, {5, 6, 7}
    for family in range(30):
        sign = "zero" if family in zero else ("positive" if family in positive else "negative")
        name = f"C1RouteARepairedOwnerCorrectionD22683Family{family}"
        (OUT / f"{name}.lean").write_text(
            render_family(template, family, factors[family], sign),
            encoding="utf-8",
            newline="\n",
        )
        (OUT / f"{name}Audit.lean").write_text(
            f"import ConnesWeilRH.Dev.{name}\n\n"
            "namespace ConnesWeilRH.Dev\n\n"
            f"#print axioms record2683Family{family}D2FactorMem\n"
            f"#print axioms record2683Family{family}CorrectionD2CellRectMem\n\n"
            "end ConnesWeilRH.Dev\n",
            encoding="utf-8",
            newline="\n",
        )
    (OUT / "C1RouteARepairedOwnerCorrectionD22683Consumer.lean").write_text(
        render_consumer(), encoding="utf-8", newline="\n"
    )
    (OUT / "C1RouteARepairedOwnerCorrectionD22683ConsumerAudit.lean").write_text(
        "import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionD22683Consumer\n\n"
        "namespace ConnesWeilRH.Dev\n\n"
        "#print axioms record2683RepairedOwnerCorrectionD2CellContained\n\n"
        "end ConnesWeilRH.Dev\n",
        encoding="utf-8",
        newline="\n",
    )
    print("generated repaired-owner correction-D2 families 0..29")


if __name__ == "__main__":
    main()
