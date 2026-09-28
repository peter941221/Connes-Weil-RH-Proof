# 2130 — Route-B n=6 height scan

Date: 2026-09-28.

Status: SCOPED-NO-GO-FOR-FIXED-N6-HEIGHT-BAND. This is a finite numerical
scan, not a continuous-cover theorem or a producer result.

The scan keeps the record-2123 owner construction, `n = 6`, `q = 2^-14`,
support radius 16, the 595877-entry prime book, and the Route-A FFT/spline
route. It samples five heights at `dxi = 0.02`:

```text
gamma          owner   C             b             det             gate
30.424876      40      +1.170e6      +1.217e10     -5.105e19       PASS
35.000000      44      +1.798e5      +1.404e9      -3.885e17       PASS
37.586178      46      -4.443e6      -1.386e10     -8.741e20       FAIL
40.918719      49      +3.667e6      +1.552e10     -7.043e20       PASS
43.327073      51      +2.711e5      -2.131e10     -6.068e20       FAIL
```

Prime coverage is complete on every row, but the sign pair is not height
stable. Therefore the unchanged fixed-`n=6` Route-B family cannot be promoted
to a continuous height cover. Combined with record 2128, this closes the
current fixed-n Route-B reopening as a route choice, not as a global no-go for
all phase-balanced constructions.

The project priority returns to the active Route-A same-owner C3' signed
margin and its actual owner/model transfer.

Reproduce:

```text
python3 scripts/routeb_n6_height_scan_2130.py
```

Artifact: `results/2130_routeb_n6_height_scan.json`.