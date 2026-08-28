# CC20 Equation-(115) source reader

This directory turns the two numerical DOCX files linked by Connes--Consani,
section 6, into a deterministic source manifest.  It is an input-validation
step for a future strict equation-(115) certificate, not that certificate.

Primary source:

- Paper: <https://arxiv.org/html/2006.13771>, equations (114)--(115).
- Angles: <https://www.dropbox.com/s/kjmra7t9ejet1pw/rangles5000.docx?dl=0>.
- Coefficients: <https://www.dropbox.com/s/e2bswzrh3tps00h/coefficients.docx?dl=0>.

The paper fixes `m = 1732`.  The published angle document contains 1,733
numeric tokens, with an exact final `1733` sentinel.  The coefficient document
also contains 1,733 numeric tokens.  Equation (114) uses entries `1` through
`m` from each list; the reader preserves both unused terminal records in the
manifest so that truncation is explicit rather than silent.

The reader accepts only the published SHA-256 digests and DOCX/XML layout.  It
parses Mathematica decimal notation into exact rational numerator/denominator
pairs and attaches a source string to every emitted entry.  It rejects changed
files, malformed notation, an unexpected count, or an unexpected angle
sentinel.

Example:

```text
python3 scripts/cc20_eq115/extract_source.py \
  --angles rangles5000.docx \
  --coefficients coefficients.docx \
  --out cc20_eq115_manifest.json
```

The manifest does not provide the missing strict data for `lambda`, the
analytic `chi`, or `integral |tau - chi|`.  Fact 1 in the paper states only
an asymptotic decimal `~0.00122`; it is not a Lean-ready inequality.

## Data and Lean table generator

The `data/` directory holds the validated inputs and their deterministic
manifest:

- `rangles5000.docx`, `coefficients.docx` - the published DOCX inputs,
  byte-identical to the Dropbox originals; the extractor re-checks both
  SHA-256 digests on every run.
- `cc20_eq115_manifest.json` - the deterministic extractor output, with one
  per-node source string per entry.

`gen_eq115_table.py` consumes the manifest and emits the Lean data module
`ConnesWeilRH/Dev/C1CC20Eq115Table.lean` (exact rationals only; the output
is a pure function of the manifest bytes, so regenerate rather than
hand-edit).  From the repository root:

    python3 scripts/cc20_eq115/gen_eq115_table.py
