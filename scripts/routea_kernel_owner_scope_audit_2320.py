"""Record 2320: compare the 2249 and 2308 kernel-owner scopes.

This is a scope audit, not a sign certificate. It refuses to combine the two
records unless their support-derived prime-power books and owner parameters
match exactly.
"""
import hashlib
import importlib
import json
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

r2249 = importlib.import_module("routea_weighted_zero_l1_enclosure_2249")
e2308 = importlib.import_module("routea_hgap_window_cert_2308")


def digest_pairs(pairs):
    payload = "\n".join(f"{int(n)}:{float(w).hex()}" for n, w in pairs).encode()
    return hashlib.sha256(payload).hexdigest()


def family_digest(families):
    payload = "\n".join(
        f"{float(width).hex()}:{float(height).hex()}" for width, height in families
    ).encode()
    return hashlib.sha256(payload).hexdigest()


def main():
    rho, nodes, values, families_2249 = r2249.build()
    carrier = e2308.evaluator.bridge.refined.remainder.carrier
    source = carrier.SOURCE
    _, families_2308, _, _ = source.load_owner()

    support_2249 = 2.0 * max(width for width, _ in families_2249)
    support_2308 = 2.0 * max(width * width for width, _ in families_2308)
    primes_2249 = r2249.r59.rig.prime_powers_up_to(math.exp(support_2249))
    primes_2308 = source.rig.prime_powers_up_to(math.exp(support_2308))

    numbers_2249 = [int(n) for n, _ in primes_2249]
    numbers_2308 = [int(n) for n, _ in primes_2308]
    weights_2249 = [float(w) for _, w in primes_2249]
    weights_2308 = [float(w) for _, w in primes_2308]

    family_equal = len(families_2249) == len(families_2308) and all(
        float(a).hex() == float(b).hex() and float(c).hex() == float(d).hex()
        for (a, c), (b, d) in zip(families_2249, families_2308)
    )
    number_equal = numbers_2249 == numbers_2308
    weight_equal = len(weights_2249) == len(weights_2308) and all(
        a.hex() == b.hex() for a, b in zip(weights_2249, weights_2308)
    )

    result = {
        "record": 2320,
        "verdict": "SAME_SCOPE" if family_equal and number_equal and weight_equal else "SCOPE_MISMATCH",
        "owner_family_equal": family_equal,
        "owner_family_count_2249": len(families_2249),
        "owner_family_count_2308": len(families_2308),
        "owner_family_digest_2249": family_digest(families_2249),
        "owner_family_digest_2308": family_digest(families_2308),
        "support_2249": support_2249,
        "support_2308": support_2308,
        "cutoff_2249": int(math.floor(math.exp(support_2249))),
        "cutoff_2308": int(math.floor(math.exp(support_2308))),
        "prime_count_2249": len(primes_2249),
        "prime_count_2308": len(primes_2308),
        "prime_numbers_equal": number_equal,
        "prime_weights_equal": weight_equal,
        "prime_numbers_digest_2249": digest_pairs(primes_2249),
        "prime_numbers_digest_2308": digest_pairs(primes_2308),
        "first_number_2249": numbers_2249[0] if numbers_2249 else None,
        "last_number_2249": numbers_2249[-1] if numbers_2249 else None,
        "first_number_2308": numbers_2308[0] if numbers_2308 else None,
        "last_number_2308": numbers_2308[-1] if numbers_2308 else None,
    }
    out = ROOT / "results" / "2320_kernel_owner_scope_audit.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result["verdict"]


if __name__ == "__main__":
    main()
