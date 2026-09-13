# 1396 — Exact-rational certificate for the 1394 witness cell of (J1)

Date: 2026-09-13. Verdict up front: **GOOD — CERT PASS**. The MODEL digit of
record [1394](1394_component5_rig_v3_valid_j1_realizable.md) section 4 is now
backed by a machine-checked inequality in **exact rational arithmetic**: the
transcendental/interval machinery is confined to a pre-comparison layer, and
the final strict inequality `C_UP < delta / (2 * D_HI)` is verified over
Python `Fraction` with no floating point at the comparison layer at all.
Script: `scripts/certify_1396_witness.py` (WSL `/usr/bin/python3.12` +
mpmath 1.4.1; rerunnable; exit code + `CERT DONE` line).

## 1. What the certificate says

Locked cell (VERBATIM 1394 section 4 / 1393 section 2 grids):

```text
d = 1/200   delta = 1/100   Rf = Ru = 1/50   eps = eps' = 1/100
rho = 99/100 + 1054*I
```

Certified dyadic pair (2^-60 grid):

```text
ceiling  <=  C_UP   = 99529719269116324599 / 2^60   (approx 86.32827028675864)
C_min    <=  D_HIq  =          135283503 / 2^60     (approx 1.1733973408e-10)
exact-rational check:  C_UP  <  (1/200) / D_HIq
                            = 144115188075855872 / 3382087575
                            (approx 42,611,311.84)          -> PASS
```

Since `ceiling <= C_UP < (1/200)/D_HIq <= delta/(2*C_min)` (ceiling increasing
in the two `K_loc`, `delta/(2 C_min)` decreasing in `C_min`, `C_min <= D_HIq`),
the strict (J1) at this cell is a **theorem of the printed rationals plus the
1383/1378 closed forms** — the arithmetic doubt that law-65 MODEL status
carries at one cell is now retired to a 62-digit-deep enclosure.

Cross-lane fidelity (certificate vs v3 rig at the same cell):
`ceiling 86.3282702868` (cert, exact layer) vs `86.32827029` (1394 rig print);
`C_D 1.1733973408e-10` (cert) vs `1.173397341e-10` (rig) — agreement, as the
rig's 200-bit class demanded.

## 2. Method (and why each shortcut was rejected)

```text
 exact rationals (all cell data)          0.005, 0.01, 0.02, 0.99, 1054 are
        |                                 exact Fr from the start
        v
 transcendental atoms ONLY on rationals   sinh, cosh, cos, sin, exp, pi via
        |                                 mpmath dps=100, each padded +-1e-80
        |                                 (mpf -> Fraction from the exact
        |                                  binary (sign, man, exp) tuple)
        v
 Fraction interval layer                  real RI: min/max of the 4 exact
        |                                 endpoint products; complex CI:
        |                                 (ac-bd, ad+bc); division by an
        |                                 asserted-zero-free interval
        v
 K_loc by Cramer                          det4 + 16 det3, Leibniz, 24/6 term
        |                                 sums; det norm asserted > 0
        v
 dyadic final + Fraction comparison       math.ceil to 2^-60, then Fr < Fr
```

Rejected alternatives, on the record:

* `mpmath.iv` — no complex intervals; `iv.conj` does not exist; `x + 1j*y`
  on `ivmpf` coerces through float, silently destroying enclosure. (This is
  the same class of silent-loss bug that killed 1393 invocation 1.)
* Direct `Fraction(str(mpf))` — string conversion rounds and may round
  INWARD, which would break outward enclosure; `mpf._mpf_` is exact.
* `Fraction(mpf)` — TypeError: `mpf` is not a `numbers.Rational`.
* Printing the intermediate exact fractions — the +-1e-80 pads accumulate
  through the Cramer division into int->str digit counts beyond CPython's
  4300-digit guard: **the 7i landmine detonated for real** (first live fire;
  1220 was the near-miss), caught and handled by rendering intermediates as
  correctly-rounded floats and printing only the small final dyadics.

Enclosure health (printed widths): K_loc_f re/im `7.0e-62 / 3.3e-62`,
K_loc_u `2.4e-61 / 1.1e-61`, det `5.4e-83` — the solve is nowhere near
condition-limited, and the imaginary enclosures (the model-real check, G3's
assert here) pass at the 1e-40 class.

## 3. Boundary — what this does and does not certify

```text
CERTIFIES   the inequality chain of 1393 s1.5 + s1.6 + s1.7 at ONE locked
            cell, given the closed forms of records 1383 (Gram) and 1378
            (couplings) as the script transcribes them (transcription
            audited against the prereg text line by line).
DOES NOT    discharge hJ1 in Lean: a Lean proof needs the same enclosure
            expressed in kernel arithmetic (NormNum-class evaluation),
            which is a NEW formal obligation, not a re-run of this one;
            nothing in this record wires a witness into `C1RouteAlphaOwner`.
DOES NOT    touch the archimedean gate, produce detector data, or carry
            any RH inference. All numbers remain MODEL (law 65) in status:
            this cert reduces the doubt in the ARITHMETIC, and the honest
            residual doubt is TRANSCRIPTION — which is exactly the doubt
            every paper-lane closed form carries anyway.
```

## 4. Files

```text
scripts/certify_1396_witness.py     the certificate (exit 0 + "CERT DONE")
stdout capture                      quoted above (sections 1-2 numbers)
```

No Lean, no build, no rig rerun; the 1393/1394 artifacts are untouched.
