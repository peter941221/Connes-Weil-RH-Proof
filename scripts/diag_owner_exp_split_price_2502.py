"""Re-run the formal split price against corrected record-2501 inputs."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "price_2500", ROOT / "scripts/diag_owner_exp_split_price_2500.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
base.INPUTS = ROOT / "results/2501_owner_exp_split_inputs.json"

buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    base.main()
result = json.loads(buf.getvalue())
result.update({
    "record": 2502,
    "status": "CORRECTED_FORMAL_EXP_SPLIT_EXTERNAL_PRICE_NOT_A_CERTIFICATE",
    "input_record": 2501,
    "nonclaims": ["no hcell proof", "no producer GO", "no RH"],
})
(ROOT / "results/2502_owner_exp_split_price.json").write_text(
    json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps(result, indent=2))
