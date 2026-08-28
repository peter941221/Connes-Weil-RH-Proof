#!/usr/bin/env python3
"""Validate CC20's linked equation-(115) DOCX inputs and emit exact rationals.

The paper's two Dropbox links are mutable external artifacts.  This tool makes
their identity explicit before any later Lean generator is allowed to consume
the displayed decimal strings.  It does not download files and it does not
claim the paper's approximate L1 value is a rigorous enclosure.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import zipfile
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable
from xml.etree import ElementTree


M = 1732
PAPER_URL = "https://arxiv.org/html/2006.13771"
ANGLES_URL = "https://www.dropbox.com/s/kjmra7t9ejet1pw/rangles5000.docx?dl=0"
COEFFICIENTS_URL = (
    "https://www.dropbox.com/s/e2bswzrh3tps00h/coefficients.docx?dl=0"
)
ANGLES_SHA256 = "0aab652b2187f766af19ba07264a5c02da7b62b40e0b2aaa14773b06460f1ed5"
COEFFICIENTS_SHA256 = (
    "5387ede3a9de8673536d76dd4163b9c60665c929cd51923dbf812ecf128a1266"
)
WORD_NS = "http://schemas.openxmlformats.org/wordprocessingml/2006/main"
NUMBER_RE = re.compile(
    r"[-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:`(?:\d+(?:\.\d*)?|\.\d+)?)?"
    r"(?:\*\^[+-]?\d+)?"
)
NUMBER_FULL_RE = re.compile(
    r"(?P<mantissa>[-+]?(?:\d+(?:\.\d*)?|\.\d+))"
    r"(?:`(?:\d+(?:\.\d*)?|\.\d+)?)?"
    r"(?:\*\^(?P<exponent>[+-]?\d+))?\Z"
)
RESIDUE_RE = re.compile(r"[\s,{}\\]*\Z")


@dataclass(frozen=True)
class PublishedDocument:
    label: str
    path: Path
    url: str
    sha256: str


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read_docx_text(path: Path) -> str:
    try:
        with zipfile.ZipFile(path) as archive:
            xml = archive.read("word/document.xml")
    except (KeyError, OSError, zipfile.BadZipFile) as exc:
        raise ValueError(f"{path} is not a readable DOCX word/document.xml") from exc

    root = ElementTree.fromstring(xml)
    paragraphs: list[str] = []
    for paragraph in root.iter(f"{{{WORD_NS}}}p"):
        text = "".join(node.text or "" for node in paragraph.iter(f"{{{WORD_NS}}}t"))
        if text.strip():
            paragraphs.append(text)
    if not paragraphs:
        raise ValueError(f"{path} contains no nonempty Word paragraphs")
    return "\n".join(paragraphs)


def parse_mathematica_number(raw: str) -> Fraction:
    match = NUMBER_FULL_RE.fullmatch(raw)
    if match is None:
        raise ValueError(f"unsupported Mathematica number: {raw!r}")
    value = Fraction(match.group("mantissa"))
    exponent = int(match.group("exponent") or "0")
    return value * (10 ** exponent)


def read_numbers(document: PublishedDocument) -> list[tuple[str, Fraction]]:
    actual = sha256_file(document.path)
    if actual != document.sha256:
        raise ValueError(
            f"{document.label} SHA-256 mismatch: expected {document.sha256}, got {actual}"
        )
    payload = read_docx_text(document.path)
    raw_numbers = [match.group(0) for match in NUMBER_RE.finditer(payload)]
    residue = NUMBER_RE.sub("", payload)
    if not RESIDUE_RE.fullmatch(residue):
        sample = residue.strip().replace("\n", " ")[:120]
        raise ValueError(f"{document.label} has unparsed payload residue: {sample!r}")
    return [(raw, parse_mathematica_number(raw)) for raw in raw_numbers]


def source_node(
    label: str, url: str, sha256: str, index: int, raw: str, value: Fraction
) -> dict[str, str | int]:
    return {
        "index": index,
        "raw": raw,
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
        "source": f"CC20 eq-(114) {label} DOCX; url={url}; sha256={sha256}; entry={index}; raw={raw}",
    }


def manifest(angles: PublishedDocument, coefficients: PublishedDocument) -> dict[str, object]:
    angle_values = read_numbers(angles)
    coefficient_values = read_numbers(coefficients)
    expected_count = M + 1
    if len(angle_values) != expected_count:
        raise ValueError(f"angles has {len(angle_values)} entries, expected {expected_count}")
    if len(coefficient_values) != expected_count:
        raise ValueError(
            f"coefficients has {len(coefficient_values)} entries, expected {expected_count}"
        )
    angle_tail_raw, angle_tail = angle_values[-1]
    if angle_tail != Fraction(M + 1):
        raise ValueError(
            f"angles terminal sentinel is {angle_tail_raw!r}, expected exact {M + 1}"
        )

    return {
        "schema_version": 1,
        "paper_url": PAPER_URL,
        "equation": "(114)-(115)",
        "m": M,
        "angles": [
            source_node("angles", angles.url, angles.sha256, index, raw, value)
            for index, (raw, value) in enumerate(angle_values[:M], start=1)
        ],
        "coefficients": [
            source_node(
                "coefficients", coefficients.url, coefficients.sha256, index, raw, value
            )
            for index, (raw, value) in enumerate(coefficient_values[:M], start=1)
        ],
        "unused_terminal_records": {
            "angle_sentinel": source_node(
                "angles", angles.url, angles.sha256, M + 1, angle_tail_raw, angle_tail
            ),
            "coefficient_after_m": source_node(
                "coefficients",
                coefficients.url,
                coefficients.sha256,
                M + 1,
                coefficient_values[-1][0],
                coefficient_values[-1][1],
            ),
        },
        "certificate_boundary": (
            "This manifest validates displayed finite data only. It does not provide "
            "a strict lambda interval, an analytic chi enclosure, or a strict L1 bound."
        ),
    }


def self_test() -> None:
    cases = {
        "1.25`": Fraction(5, 4),
        "-3.5`20.": Fraction(-7, 2),
        "2.5*^3": Fraction(2500),
        ".125`10": Fraction(1, 8),
    }
    for raw, expected in cases.items():
        actual = parse_mathematica_number(raw)
        if actual != expected:
            raise AssertionError(f"{raw}: expected {expected}, got {actual}")


def parse_args(argv: Iterable[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--angles", type=Path, required=False)
    parser.add_argument("--coefficients", type=Path, required=False)
    parser.add_argument("--out", type=Path, required=False)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(list(argv))
    if args.self_test:
        return args
    if args.angles is None or args.coefficients is None or args.out is None:
        parser.error("--angles, --coefficients, and --out are required unless --self-test")
    return args


def main(argv: Iterable[str]) -> int:
    args = parse_args(argv)
    if args.self_test:
        self_test()
        print("self-test: ok")
        return 0

    assert args.angles is not None
    assert args.coefficients is not None
    assert args.out is not None
    if args.out.exists():
        raise ValueError(f"refusing to overwrite existing output: {args.out}")
    result = manifest(
        PublishedDocument("angles", args.angles, ANGLES_URL, ANGLES_SHA256),
        PublishedDocument(
            "coefficients", args.coefficients, COEFFICIENTS_URL, COEFFICIENTS_SHA256
        ),
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "m": result["m"],
                "angles": len(result["angles"]),
                "coefficients": len(result["coefficients"]),
                "out": str(args.out),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
