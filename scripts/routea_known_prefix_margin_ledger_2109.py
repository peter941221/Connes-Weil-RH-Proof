import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "results" / "2109_known_prefix_margin_ledger.json"
margin = 1675397327895.099
terms = {
    "finite_window_em_forward": 57204203.08066749,
    "amatrix_true_transfer": 59268.334716796875,
    "gram_true_transfer_h1_diagnostic": 17338058.88696289,
    "tail_40_to_infinity": 2.2087121764650203e-138,
}
known = sum(terms.values())
result = {
    "record": 2109,
    "status": "KNOWN-PREFIX-MARGIN-LEDGER-CANDIDATE",
    "owner": {
        "gamma": 39.25244858548658,
        "delta": 0.445,
        "scale": 0.80,
        "nodes": 30,
        "support": 5.12,
        "visible_prime_book": 52,
        "construction": "first 30 numerical zeros in closed ball; shared kill width 2.2; direct square solve",
    },
    "sampled_negative_margin": margin,
    "known_error_sum": known,
    "known_error_over_margin": known / margin,
    "remaining_margin_after_known_errors": margin - known,
    "terms": terms,
    "interpretation": [
        "direct A c = y is the unique feasible coefficient vector when A is square and nonsingular, hence it is also the H1 minimizer for the same family",
        "the Gram transfer is retained as a separate diagnostic and is not added to the direct coefficient path twice",
    ],
    "unknown_or_not_promoted": [
        "complete abstract source-zero owner rather than first-30 numerical prefix",
        "parameter-uniform owner cardinality, separation, and conditioning",
        "outward interval promotion of the direct coefficients and finite-window jet",
        "formal tail monotonicity and N48 endpoint proof for this changed family",
        "model-to-physical owner transfer for all hypothetical off-line zeros",
    ],
    "nonclaims": ["candidate ledger only", "not a producer theorem or RH proof"],
    "provenance": {
        "margin": "results/2103_full_known_prefix_direct_owner_grid_m6400.json",
        "em": "results/2105_known_prefix_em_forward_bound.json",
        "tail": "results/2106_known_prefix_tail_price.json",
        "amatrix": "results/2107_known_prefix_amatrix_transfer.json",
        "gram": "results/2108_known_prefix_gram_transfer.json",
        "script": os.fspath(Path(__file__).relative_to(ROOT)),
    },
}
with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
    json.dump(result, handle, indent=2)
    handle.write("\n")
print(json.dumps(result, indent=2))
