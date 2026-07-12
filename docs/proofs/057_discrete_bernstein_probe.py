#!/usr/bin/env python3
"""Reject lattice Bernstein/Stieltjes explanations of the Weil source.

For a Bernstein function restricted to x=n^2, adjacent secant slopes in x
must be nonincreasing.  For a discrete Bernstein sequence a_n=Phi(n^2), its
ordinary increments must also be nonincreasing.  Arb certifies that both
conditions already fail on n=1,2,3.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load module: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--loewner-probe", type=Path, required=True)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--prec", type=int, default=768)
    args = parser.parse_args()

    from flint import arb, ctx

    ctx.prec = args.prec
    upstream = load_module("arb_ldlt_upstream", args.upstream)
    loewner_probe = load_module("loewner_probe", args.loewner_probe)

    values = [
        loewner_probe.phi_at(upstream, args.c, arb(index), args.prec)
        for index in (1, 2, 3)
    ]
    raw_increment_12 = values[1] - values[0]
    raw_increment_23 = values[2] - values[1]
    raw_increment_growth = raw_increment_23 - raw_increment_12

    square_slope_12 = raw_increment_12 / arb(3)
    square_slope_23 = raw_increment_23 / arb(5)
    square_slope_growth = square_slope_23 - square_slope_12

    print(f"c={args.c} Arb_bits={args.prec}")
    for index, value in zip((1, 2, 3), values):
        print(f"Phi({index}^2)={value.str(25)}")
    print(f"raw_increment_[1,2]={raw_increment_12.str(25)}")
    print(f"raw_increment_[2,3]={raw_increment_23.str(25)}")
    print(f"raw_increment_growth={raw_increment_growth.str(25)}")
    print(f"square_secant_[1,4]={square_slope_12.str(25)}")
    print(f"square_secant_[4,9]={square_slope_23.str(25)}")
    print(f"square_secant_growth={square_slope_growth.str(25)}")

    if not raw_increment_growth > 0:
        raise AssertionError("expected discrete Bernstein increment failure")
    if not square_slope_growth > 0:
        raise AssertionError("expected squared-node concavity failure")
    print("discrete_bernstein_route=rejected")
    print("squared_node_stieltjes_route=rejected")


if __name__ == "__main__":
    main()
