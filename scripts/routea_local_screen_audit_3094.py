#!/usr/bin/env python3
"""Build the Route A local screen and check the reported theorem axioms.

Run with Python 3 from a Linux checkout with the pinned Lean toolchain.
The JSON result contains no machine paths; the full local build log is kept
separately for diagnostics.
"""

import json
from pathlib import Path
import re
import subprocess
import sys


MODULES = [
    "C1C3SigmaZeroMargin3090Audit",
    "C1RouteAJointSymbolContinuity3091Audit",
    "C1RouteAOwnerAnalyticTransform3092Audit",
    "C1RouteANegativeEnergyWitness3093Audit",
    "C1RouteAReadbackNormalization3094Audit",
    "C1RouteAJointSymbolReadback3081Audit",
    "C1RouteAJointSymbolSquareScreen3082Audit",
    "C1RouteANonzeroNegativeEnergy3084Audit",
    "C1RouteAAnalyticPuncturedWitness3085Audit",
    "C1RouteALaplaceFourierBridge3086Audit",
    "C1RouteAOwnerPuncturedBridge3087Audit",
    "C1RouteAJointSymbolNegativeNeighbourhood3088Audit",
    "C1RouteAZeroFrequencyMargin3089Audit",
    "C1G8MasterExitAudit",
]

REQUIRED = [
    "ConnesWeilRH.Dev.C1C3SigmaZeroMargin3090.c3Sigma_zero_pos",
    "ConnesWeilRH.Source.C1RouteAJointSymbolContinuity3091."
    "routeAJointSymbol_continuousAt_zero",
    "ConnesWeilRH.Source.C1RouteAOwnerAnalyticTransform3092."
    "routeAOrbitTransform_analytic",
    "ConnesWeilRH.Source.C1RouteAOwnerAnalyticTransform3092."
    "routeAOrbitTransform_global_nonzero",
    "ConnesWeilRH.Source.C1RouteANegativeEnergyWitness3093."
    "exists_nonzero_frequency_negative_energy_witness",
    "ConnesWeilRH.Source.C1RouteANegativeEnergyWitness3093."
    "not_routeAFrequencyEnergyDensity_pointwise_nonneg",
    "ConnesWeilRH.Source.C1RouteANegativeEnergyWitness3093Audit."
    "empty_prime_set_zero_margin",
    "ConnesWeilRH.Source.C1RouteANegativeEnergyWitness3093Audit."
    "energy_at_zero_eq_zero_of_off_line",
    "ConnesWeilRH.Source.C1RouteANegativeEnergyWitness3093Audit."
    "no_localWitness_when_transform_vanishes_on_its_ball",
    "ConnesWeilRH.Source.C1RouteAReadbackNormalization3094."
    "routeAOrbitTransform_squared_mass",
    "ConnesWeilRH.Source.C1RouteAReadbackNormalization3094."
    "routeA_normalized_squared_mass",
    "ConnesWeilRH.Source.C1RouteAReadbackNormalization3094."
    "routeA_unscaled_squared_mass_ne_square_at_zero",
    "ConnesWeilRH.Source.C1RouteAReadbackNormalization3094."
    "exists_normalized_negative_energy_density",
]


def main():
    root = Path(__file__).resolve().parents[1]
    results = root / "results"
    results.mkdir(exist_ok=True)
    command = ["lake", "build"] + ["ConnesWeilRH.Dev." + m for m in MODULES]
    build = subprocess.run(command, cwd=root, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True, encoding="utf-8")
    log = build.stdout
    (results / "3094_routea_local_screen_build.log").write_text(log, encoding="utf-8")
    declarations = {
        name: [a.strip() for a in axioms.split(",") if a.strip()]
        for name, axioms in re.findall(
            r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log
        )
    }
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    unexpected = {n: a for n, a in declarations.items() if set(a) != allowed}
    missing = [name for name in REQUIRED if name not in declarations]
    completed = re.search(r"Build completed successfully \((\d+) jobs\)", log)
    passed = (build.returncode == 0 and completed is not None
              and not re.search(r"^error:", log, re.MULTILINE)
              and "sorryAx" not in log and not missing and not unexpected)
    report = {
        "status": "PASS" if passed else "FAIL",
        "modules": command[2:],
        "build_returncode": build.returncode,
        "build_jobs": int(completed.group(1)) if completed else None,
        "sorryAx_present": "sorryAx" in log,
        "required_theorems": {n: declarations[n] for n in REQUIRED if n in declarations},
        "all_reported_axiom_declarations": len(declarations),
        "unexpected_axioms": unexpected,
        "missing_required_theorems": missing,
        "scope": "Local negative density and Fourier normalization; no qw sign or RH proof.",
    }
    artifact = results / "3094_routea_local_screen_audit.json"
    artifact.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
