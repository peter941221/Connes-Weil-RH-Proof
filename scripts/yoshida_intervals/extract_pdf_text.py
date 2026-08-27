#!/usr/bin/env python3
"""Extract text from a PDF into a plain-text file (pypdf, UTF-8)."""

import sys

from pypdf import PdfReader


def main() -> None:
    src, dst = sys.argv[1], sys.argv[2]
    reader = PdfReader(src)
    chunks = []
    for index, page in enumerate(reader.pages):
        text = page.extract_text() or ""
        chunks.append(f"\n===== PAGE {index + 1} =====\n" + text)
    joined = "\n".join(chunks)
    with open(dst, "w", encoding="utf-8") as handle:
        handle.write(joined)
    print(f"pages={len(reader.pages)} chars={len(joined)}")


if __name__ == "__main__":
    main()
