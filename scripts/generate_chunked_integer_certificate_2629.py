"""Generate an auditable base-10^9 multiplication/carry certificate."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


BASE = 10**9


def split_chunks(value: int, base: int = BASE) -> list[int]:
    if value < 0:
        raise ValueError("split_chunks expects nonnegative integers")
    if value == 0:
        return [0]
    chunks: list[int] = []
    while value:
        value, digit = divmod(value, base)
        chunks.append(digit)
    return chunks


def multiply_with_carries(left: int, right: int, base: int = BASE) -> dict:
    if left < 0 or right < 0:
        raise ValueError("certificate operands must be nonnegative")
    left_chunks = split_chunks(left, base)
    right_chunks = split_chunks(right, base)
    raw_rows = [0] * (len(left_chunks) + len(right_chunks) - 1)
    local_products: list[dict] = []
    for left_index, left_digit in enumerate(left_chunks):
        for right_index, right_digit in enumerate(right_chunks):
            row = left_index + right_index
            product = left_digit * right_digit
            raw_rows[row] += product
            local_products.append({
                "left_index": left_index,
                "right_index": right_index,
                "row": row,
                "left_digit": left_digit,
                "right_digit": right_digit,
                "product": product,
            })

    digits: list[int] = []
    carry_rows: list[dict] = []
    carry = 0
    for row, product_sum in enumerate(raw_rows):
        raw = product_sum + carry
        digit = raw % base
        next_carry = raw // base
        carry_rows.append({
            "row": row,
            "product_sum": product_sum,
            "carry_in": carry,
            "raw": raw,
            "digit": digit,
            "carry_out": next_carry,
        })
        digits.append(digit)
        carry = next_carry
    while carry:
        digits.append(carry % base)
        carry //= base

    reconstructed = sum(digit * base**index for index, digit in enumerate(digits))
    if reconstructed != left * right:
        raise AssertionError("chunk reconstruction does not equal the product")
    for row in carry_rows:
        if row["raw"] != row["product_sum"] + row["carry_in"]:
            raise AssertionError("raw-row identity failed")
        if row["raw"] != row["digit"] + base * row["carry_out"]:
            raise AssertionError("carry-row identity failed")

    return {
        "base": base,
        "left": str(left),
        "right": str(right),
        "left_chunks": left_chunks,
        "right_chunks": right_chunks,
        "local_products": local_products,
        "carry_rows": carry_rows,
        "result_chunks": digits,
        "reconstructed": str(reconstructed),
    }


def render_lean_local_certificate(certificate: dict, theorem_name: str) -> str:
    """Render local product and carry rows as small Lean arithmetic facts."""
    base = certificate["base"]
    facts: list[str] = []
    for row in certificate["local_products"]:
        facts.append(
            f"({row['left_digit']} * {row['right_digit']} = {row['product']})"
        )
    products_by_row: dict[int, list[int]] = {}
    for row in certificate["local_products"]:
        products_by_row.setdefault(row["row"], []).append(row["product"])
    for row in certificate["carry_rows"]:
        products = products_by_row.get(row["row"], [])
        product_sum = " + ".join(str(product) for product in products) or "0"
        facts.append(f"{product_sum} = {row['product_sum']}")
    for row in certificate["carry_rows"]:
        facts.append(
            f"{row['raw']} = {row['product_sum']} + {row['carry_in']}"
        )
        facts.append(
            f"{row['raw']} = {row['digit']} + {base} * {row['carry_out']}"
        )
    def render_chunks(chunks: list[int]) -> str:
        terms = [f"{digit} * {base} ^ {index}" for index, digit in enumerate(chunks)]
        return " + ".join(terms)

    lines = ["import Mathlib.Tactic.NormNum", "", "namespace ConnesWeilRH.Dev", ""]
    lines.extend([
        f"theorem {theorem_name}_left_decomposition :",
        f"  ({certificate['left']} : ℕ) = {render_chunks(certificate['left_chunks'])} := by",
        "  norm_num",
        "",
        f"theorem {theorem_name}_right_decomposition :",
        f"  ({certificate['right']} : ℕ) = {render_chunks(certificate['right_chunks'])} := by",
        "  norm_num",
        "",
        f"theorem {theorem_name}_result_reconstruction :",
        f"  ({certificate['reconstructed']} : ℕ) = {render_chunks(certificate['result_chunks'])} := by",
        "  norm_num",
        "",
    ])
    for index, fact in enumerate(facts):
        lines.extend([
            f"theorem {theorem_name}_{index:03d} : {fact} := by",
            "  norm_num",
            "",
        ])
    lines.extend(["end ConnesWeilRH.Dev", ""])
    return chr(10).join(lines) + chr(10)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--left", type=int, required=True)
    parser.add_argument("--right", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-output", type=Path)
    parser.add_argument("--lean-theorem", default="chunkedIntegerCertificate2629")
    args = parser.parse_args()
    certificate = multiply_with_carries(args.left, args.right)
    args.output.write_text(json.dumps(certificate, indent=2) + chr(10), encoding="utf-8")
    if args.lean_output is not None:
        args.lean_output.write_text(
            render_lean_local_certificate(certificate, args.lean_theorem),
            encoding="utf-8",
        )


if __name__ == "__main__":
    main()
