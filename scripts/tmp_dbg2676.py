import struct, sys
sys.path.insert(0, "scripts")
from routea_cell4096_containment_2676 import parse_fin30_rationals, load_module
from pathlib import Path
ROOT = Path(".")
strip = load_module("s", ROOT/"scripts/routea_corrected_strip_envelope_2303.py")
fam, b, c, an = strip.load_owner()
theta = parse_fin30_rationals(ROOT/"ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean", "capturedModulations2584")
width = parse_fin30_rationals(ROOT/"ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean", "storedWidth")
for j in range(30):
    m, p = theta[j], fam[j][1]
    ok = struct.pack(">d", float(m)) == struct.pack(">d", p)
    if not ok:
        print(f"j={j}: lean={m} = {float(m)!r}  cap={p!r}  hex={fam[j][1].hex()}")
print("width all ok:", all(struct.pack(">d", float(width[j]))==struct.pack(">d", fam[j][0]) for j in range(30)))
