"""Record 2321: signed omitted-prime-book contribution on the 2249 owner grid.

This is a parameterized diagnostic for the exact question left by record 2320:
what does the 2308 prime book add to the 2249 finite-window functional when
all owner transforms and the annihilator are kept fixed? It is not yet a
certified enclosure.
"""
import hashlib
import importlib
import json
import math
import os
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
r2249 = importlib.import_module("routea_weighted_zero_l1_enclosure_2249")
e2308 = importlib.import_module("routea_hgap_window_cert_2308")


def main():
    rho, nodes, values, families = r2249.build()
    step = float(os.environ.get("GRID_STEP", "0.01"))
    grid = np.arange(-r2249.XMAX, r2249.XMAX + step / 2, step)
    xw_cache = {}
    xw = []
    for width, _ in families:
        if float(width) not in xw_cache:
            xw_cache[float(width)] = r2249.phi_weights_cached(width)
        xw.append(xw_cache[float(width)])
    matrix = r2249.r80.family_values(
        families, r2249.K, np.asarray(nodes, complex), xw
    ).T
    base = np.linalg.solve(matrix, np.ones(len(nodes), complex))
    correction = np.linalg.solve(matrix, np.asarray(values, complex))
    values_grid = r2249.r80.family_values(
        families, r2249.K, 0.5 - 2j * np.pi * grid, xw
    )
    base_laplace = base @ values_grid
    correction_laplace = correction @ values_grid
    annihilator = np.real(r2249.r59.P_from_nodes(
        grid, r2249.r80.counterpart_nodes(rho)
    ))
    owner_weight = annihilator * annihilator
    owner_weight *= np.abs(base_laplace) ** 2
    owner_weight *= np.abs(correction_laplace) ** 2

    short_primes = r2249.r59.rig.prime_powers_up_to(
        math.exp(2 * max(width for width, _ in families))
    )
    carrier = e2308.evaluator.bridge.refined.remainder.carrier
    source = carrier.SOURCE
    full_kernel, full_count = source.prime_kernel(
        grid, 2.0 * max(width * width for width, _ in families)
    )
    short_kernel = r2249.r59.rig.sigma_vec(2.0 * np.pi * grid)
    for number, weight in short_primes:
        short_kernel += 2.0 * weight / math.sqrt(number) * np.cos(
            2.0 * np.pi * grid * math.log(number)
        )
    omitted_kernel = full_kernel - short_kernel
    integrand = omitted_kernel * owner_weight
    signed_delta = float(np.trapezoid(integrand, grid))
    block_abs = {}
    for block in (0.1, 0.2, 0.5, 1.0, 2.0):
        step_count = int(round(block / step))
        total = 0.0
        for start in range(0, grid.size - 1, step_count):
            stop = min(start + step_count, grid.size - 1)
            total += abs(float(np.trapezoid(integrand[start:stop + 1], grid[start:stop + 1])))
        block_abs[str(block)] = total
    abs_delta = float(np.trapezoid(np.abs(omitted_kernel * owner_weight), grid))
    short_value = float(np.trapezoid(
        short_kernel * owner_weight, grid
    ))
    full_value = float(np.trapezoid(
        full_kernel * owner_weight, grid
    ))
    full_primes = source.rig.prime_powers_up_to(math.exp(2.0 * max(width * width for width, _ in families)))
    numbers = np.asarray([number for number, _ in full_primes], dtype=np.int64)
    lam = np.asarray([weight for _, weight in full_primes], dtype=float)
    omitted_mask = numbers > int(short_primes[-1][0])
    omitted_numbers = numbers[omitted_mask]
    omitted_lam = lam[omitted_mask]
    phi = 2.0 * np.pi * np.log(omitted_numbers.astype(float))
    term_values = np.empty(phi.size, dtype=float)
    for start in range(0, phi.size, 256):
        stop = min(start + 256, phi.size)
        phases = phi[start:stop, None] * grid[None, :]
        term_values[start:stop] = 2.0 * omitted_lam[start:stop] / np.sqrt(omitted_numbers[start:stop]) * np.trapezoid(np.cos(phases) * owner_weight[None, :], grid, axis=1)
    frequency_group_abs = {}
    for width_group in (0.5, 1.0, 2.0, 4.0, 8.0):
        groups = np.floor(phi / width_group).astype(np.int64)
        grouped = {}
        for group, value in zip(groups, term_values):
            grouped[group] = grouped.get(int(group), 0.0) + float(value)
        frequency_group_abs[str(width_group)] = float(sum(abs(value) for value in grouped.values()))
    term_signed = float(np.sum(term_values))
    term_abs = float(np.sum(np.abs(term_values)))
    result = {
        "record": 2323,
        "grid_points": int(grid.size),
        "grid_step": step,
        "family_count": len(families),
        "short_prime_count": len(short_primes),
        "full_prime_count": int(full_count),
        "short_cutoff": int(short_primes[-1][0]),
        "full_cutoff": int(max(number for number, _ in source.rig.prime_powers_up_to(
            math.exp(2.0 * max(width * width for width, _ in families))
        ))),
        "short_value": short_value,
        "full_value": full_value,
        "signed_omitted_delta": signed_delta,
        "fourier_term_signed": term_signed,
        "fourier_term_abs_sum": term_abs,
        "frequency_group_abs_sum": frequency_group_abs,
        "absolute_omitted_charge": abs_delta,
        "block_signed_integral_abs_sum": block_abs,
        "delta_over_abs_full": abs_delta / max(abs(full_value), 1e-300),
        "owner_family_digest": hashlib.sha256(
            "\n".join(f"{float(a).hex()}:{float(b).hex()}" for a, b in families).encode()
        ).hexdigest(),
        "status": "REFINEMENT_DIAGNOSTIC_NOT_CERTIFICATE",
    }
    out = ROOT / "results" / "2323_fourier_refinement_0p01.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
