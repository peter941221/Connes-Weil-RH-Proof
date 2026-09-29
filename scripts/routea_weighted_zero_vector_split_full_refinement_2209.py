"""Record 2209: full-owner vector split refinement at NSEG=1100."""
import importlib.util
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sp = importlib.util.spec_from_file_location(
    "full2206", ROOT / "scripts" / "routea_weighted_zero_vector_split_full_refinement_2206.py")
m = importlib.util.module_from_spec(sp)
sp.loader.exec_module(m)
m.NSEG = 1100

if __name__ == "__main__":
    m.OUT = ROOT / "results" / "2209_weighted_zero_vector_split_full_refinement.json"
    # Preserve the parent implementation and its explicit artifact name.
    m.main()

