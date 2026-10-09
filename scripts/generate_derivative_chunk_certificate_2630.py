"""Generate exact chunk ledgers for derivative/denominator coefficient replay.

This is an arithmetic input certificate only. It deliberately does not claim
that the complete polynomial replay or owner assembly has been proved in Lean.
"""
from __future__ import annotations

import argparse
import json
import re
from fractions import Fraction
from pathlib import Path

BASE = 10**9
BLOCK_SIZE = 8
ROOT = Path(__file__).resolve().parents[1]


def parse_list(source: str, name: str) -> list[Fraction]:
    marker = f"def {name} : List ℚ := ["
    start = source.index(marker) + len(marker)
    depth = 1
    index = start
    while depth:
        if source[index] == "[":
            depth += 1
        elif source[index] == "]":
            depth -= 1
        index += 1
    body = source[start:index - 1]
    parts: list[str] = []
    begin = 0
    paren = 0
    for position, char in enumerate(body):
        if char == "(":
            paren += 1
        elif char == ")":
            paren -= 1
        elif char == "," and paren == 0:
            parts.append(body[begin:position].strip())
            begin = position + 1
    parts.append(body[begin:].strip())
    values = []
    for part in parts:
        match = re.fullmatch(r"\(\((-?\d+) : ℚ\) / (\d+)\)", part)
        if match is None:
            raise ValueError(f"cannot parse rational entry: {part[:80]}")
        values.append(Fraction(int(match.group(1)), int(match.group(2))))
    return values


def chunks(value: int) -> list[int]:
    if value < 0:
        raise ValueError("chunk certificate expects nonnegative integers")
    result = []
    while value:
        value, digit = divmod(value, BASE)
        result.append(digit)
    return result or [0]


def block_values(value_chunks: list[int], block_size: int = BLOCK_SIZE) -> list[dict]:
    blocks = []
    for index in range(0, len(value_chunks), block_size):
        block_chunks = value_chunks[index:index + block_size]
        value = sum(digit * BASE ** offset for offset, digit in enumerate(block_chunks))
        blocks.append({
            "index": index // block_size,
            "start_chunk": index,
            "chunks": block_chunks,
            "value": value,
        })
    return blocks


def ledger(left: int, right: int) -> dict:
    left_chunks = chunks(left)
    right_chunks = chunks(right)
    products = [0] * (len(left_chunks) + len(right_chunks) - 1)
    local_products = []
    for left_index, left_digit in enumerate(left_chunks):
        for right_index, right_digit in enumerate(right_chunks):
            row = left_index + right_index
            product = left_digit * right_digit
            products[row] += product
            local_products.append({
                "left_index": left_index,
                "right_index": right_index,
                "row": row,
                "product": product,
            })
    carry_rows = []
    carry = 0
    result_chunks = []
    for row, product_sum in enumerate(products):
        raw = product_sum + carry
        digit, next_carry = divmod(raw, BASE)
        carry_rows.append({
            "row": row,
            "product_sum": product_sum,
            "carry_in": carry,
            "raw": raw,
            "digit": digit,
            "carry_out": next_carry,
        })
        result_chunks.append(digit)
        carry = next_carry
    while carry:
        digit, carry = divmod(carry, BASE)
        result_chunks.append(digit)
    reconstructed = sum(digit * BASE**index for index, digit in enumerate(result_chunks))
    if reconstructed != left * right:
        raise AssertionError("chunk reconstruction failed")
    return {
        "base": BASE,
        "left": str(left),
        "right": str(right),
        "left_blocks": block_values(left_chunks),
        "right_blocks": block_values(right_chunks),
        "left_chunks": left_chunks,
        "right_chunks": right_chunks,
        "local_products": local_products,
        "carry_rows": carry_rows,
        "result_chunks": result_chunks,
        "reconstructed": str(reconstructed),
    }


def coefficient_certificate(panel: int, coefficient: int) -> dict:
    source = (ROOT / f"ConnesWeilRH/Dev/C1RouteAMomentPanelTable2622K04Panel{panel:03d}.lean").read_text(encoding="utf-8")
    polynomial = parse_list(source, f"momentPanelPolynomial2622K04P{panel:03d}")
    primitive = parse_list(source, f"momentPanelPrimitive2622K04P{panel:03d}")
    if not 0 <= coefficient < len(polynomial) - 1:
        raise ValueError("coefficient must have a successor primitive slot")
    left = (coefficient + 1) * primitive[coefficient + 1]
    right = polynomial[coefficient]
    if left != right:
        raise AssertionError(f"derivative identity failed at coefficient {coefficient}")
    return {
        "panel": panel,
        "coefficient": coefficient,
        "identity": f"({coefficient + 1}) * primitive[{coefficient + 1}] = polynomial[{coefficient}]",
        "left_numerator": left.numerator,
        "left_denominator": left.denominator,
        "right_numerator": right.numerator,
        "right_denominator": right.denominator,
        "canonical_operands": {
            "left_numerator_chunks": chunks(left.numerator),
            "right_numerator_chunks": chunks(right.numerator),
            "left_denominator_chunks": chunks(left.denominator),
            "right_denominator_chunks": chunks(right.denominator),
            "left_numerator_blocks": block_values(chunks(left.numerator)),
            "right_numerator_blocks": block_values(chunks(right.numerator)),
            "left_denominator_blocks": block_values(chunks(left.denominator)),
            "right_denominator_blocks": block_values(chunks(right.denominator)),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--panel", type=int, default=2)
    parser.add_argument("--coefficients", type=int, nargs="+", default=[0, 32])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    records = [coefficient_certificate(args.panel, coefficient) for coefficient in args.coefficients]
    payload = {"record": 2630, "panel": args.panel, "certificates": records}
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(args.output)
    for record in records:
        operands = record["canonical_operands"]
        print(f"panel={args.panel} coefficient={record['coefficient']} "
              f"numerator_chunks={len(operands['left_numerator_chunks'])} "
              f"denominator_chunks={len(operands['left_denominator_chunks'])} "
              f"numerator_blocks={len(operands['left_numerator_blocks'])} "
              f"denominator_blocks={len(operands['left_denominator_blocks'])} "
              "canonical_fraction_equal=True")


if __name__ == "__main__":
    main()
