"""Record 2210: NSEG=1100 rounding allowance on the binding correction row."""
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sp = importlib.util.spec_from_file_location(
    "a2207", ROOT / "scripts" / "routea_weighted_zero_vector_rounding_allowance_2207.py")
m = importlib.util.module_from_spec(sp)
sp.loader.exec_module(m)
m.NSEG = 1100
m.OUT = ROOT / "results" / "2210_weighted_zero_vector_rounding_allowance.json"

if __name__ == "__main__":
    m.main()

