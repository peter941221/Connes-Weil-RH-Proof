"""Generate coordinate-bound certificate rows for the record-2623 batch.

Emits the record-2617 coordinate-leaf shape for whole rows of the static
defect comparison: per-row product cache, six-block sum modules, four
coordinate sums per entry, direct entry bounds with audits, and the
same-name row facade that keeps the record-2600 consumer names.
"""

import argparse
import json

from generate_static_coordinate_bounds_2617 import (
    DEV,
    WITNESS,
    CONVERTED_ROWS,
    generated_row_sources,
)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rows", default="1,2,3,4,5")
    arguments = parser.parse_args()
    rows = [int(value) for value in arguments.rows.split(",")]
    if any(row not in CONVERTED_ROWS or row == 0 for row in rows):
        raise ValueError("rows must be converted, nonzero indices in [1, 29]")
    payload = json.loads(WITNESS.read_text(encoding="utf-8"))
    for row in rows:
        for filename, source in generated_row_sources(payload, row).items():
            output = DEV / filename
            output.write_text(source, encoding="utf-8", newline="\n")
            print(output.relative_to(DEV.parent.parent), flush=True)


if __name__ == "__main__":
    main()
