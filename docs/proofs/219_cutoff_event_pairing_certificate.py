#!/usr/bin/env python3
"""Certify failures of positive cutoff-interval pairing.

The exact cutoff-free Weil matrix builder comes from the reproduction package
for arXiv:2607.02828.  For consecutive prime-power cutoffs c0 < c1, this
script evaluates Q_N(c1)-Q_N(c0) in two source coordinates:

* the scalar N=0 coordinate;
* the normalized odd vector (e_-1-e_1)/sqrt(2) at N=1.

A strictly negative Arb interval in either coordinate rules out a positive
semidefinite increment on that sector.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


DEFAULT_PAIRS = "2:3,3:4,4:5,5:7,7:8,8:9,9:11,11:13"


def load_upstream(path: Path):
    spec = importlib.util.spec_from_file_location("arb_ldlt_upstream", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load upstream module: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def parse_pairs(raw: str) -> list[tuple[int, int]]:
    pairs = []
    for item in raw.split(","):
        left, right = item.split(":", maxsplit=1)
        pairs.append((int(left), int(right)))
    return pairs


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--pairs", default=DEFAULT_PAIRS)
    parser.add_argument("--prec", type=int, default=512, help="Arb bits")
    args = parser.parse_args()

    from flint import ctx

    ctx.prec = args.prec
    upstream = load_upstream(args.upstream)
    source_hash = hashlib.sha256(args.upstream.read_bytes()).hexdigest()
    print(f"upstream_sha256={source_hash}")
    print(f"arb_bits={args.prec}")

    certified_negative_count = 0
    for left, right in parse_pairs(args.pairs):
        scalar_left, _ = upstream.build_arb_tau(left, 0, args.prec)
        scalar_right, _ = upstream.build_arb_tau(right, 0, args.prec)
        scalar_delta = scalar_right[0, 0] - scalar_left[0, 0]

        odd_left, _ = upstream.build_arb_tau(left, 1, args.prec)
        odd_right, _ = upstream.build_arb_tau(right, 1, args.prec)
        delta = odd_right - odd_left
        odd_rayleigh = (
            delta[0, 0]
            + delta[2, 2]
            - delta[0, 2]
            - delta[2, 0]
        ) / 2

        scalar_negative = bool(scalar_delta < 0)
        odd_negative = bool(odd_rayleigh < 0)
        certified_negative_count += int(scalar_negative or odd_negative)
        print(
            f"pair={left}->{right} "
            f"scalar={scalar_delta.str(24)} "
            f"scalar_negative={scalar_negative} "
            f"odd={odd_rayleigh.str(24)} "
            f"odd_negative={odd_negative}"
        )

    if certified_negative_count == 0:
        raise RuntimeError("no negative cutoff increment was certified")
    print(f"certified_negative_pairs={certified_negative_count}")


if __name__ == "__main__":
    main()
