# Record 1333 — Official verdict of the record-1332 probe, and the winding identification

Date: 2026-09-11.
Status: VERDICT RECORD for the official run of the record 1332 section 4
protocol (with Amendment A1). The run is archived at
`docs/proofs/1332_probe_results.json`. Paper analysis only; no Lean brick;
no new numerics authorized here (a separate preregistration record follows).
RH is not claimed.

## 1. Official verdict: INCONCLUSIVE

Verbatim rule (1332 section 4): NONTRIVIAL-LIKELY requires
`sigma_min(L=64,N=4096) < 1e-4` AND `sigma_min(4096) < 0.5*sigma_min(2048)`
at L=64 AND at least two main cells with `sigma_min < 1e-4`. The run
satisfied cells 1 and 3 but failed the monotonicity clause:
`2.33e-17 vs 0.5*3.39e-17 = 1.69e-17`. Since the rule failed, and the
TRIVIAL-LIKELY alternative (`sigma_min >= 1e-2` in every N >= 2048 cell)
also fails, the registered verdict is **INCONCLUSIVE**.

The failure mechanism is a design defect, not a data ambiguity:
`sigma_min` saturated at the machine floor (~1e-16 relative to
`||T|| = 1`) in every main cell, where a "strictly decreasing" comparison
between two floor values is meaningless. The informative statistic in this
regime is the CLIFF COUNT below the floor, not the floor value.

## 2. What the run actually shows

Controls (all passed, proving the conventions and normalization):

```text
C1 phi=1      : sigma_min = 1.000000  (identity witness, per A1)
C2 unit +shift: exactly one sigma <= 1e-15 (edge column), rest = 1
C3/C4 0.1-rad : sigma_min = 0.9988 >= 0.5 (Helson-Szego regime)
```

Main cells (`c2` = count of singular values < 1e-2; every cliff value is at
the machine floor: `c6 ~ c2`, i.e. these are zero singular values, not
decaying ones):

```text
+-----------+-------+-------+-------+----------------------------------+
| cell      | c2=512| 1024  | 2048  | 4096                             |
+-----------+-------+-------+-------+----------------------------------+
| L=32      |   87  |  383  |  388  | 388   (saturated at N=2048)      |
| L=64      |   91  |  134  |  838  | 954   (NOT yet saturated)        |
+-----------+-------+-------+-------+----------------------------------+
```

The winding identification: the continuous-branch total phase winding of
the committed scattering phase `phi` over `[-L, L]`,
`W(L) = (arg phi(L) - arg phi(-L)) / 2pi` evaluated by 200001-point
unwrap of `-2 Im logGamma_R(1/2 + 2 pi i x)`:

```text
+------+--------------------+------------------+------------------------+
| L    |  -W(L)             |  count c2 (best) | ratio                  |
+------+--------------------+------------------+------------------------+
| 32   |  388.9             |  388             | 0.9977                 |
| 48   |  661.2             |  (not probed)    |                        |
| 64   |  955.2             |  954             | 0.9987                 |
+------+--------------------+------------------+------------------------+
```

Reading: for a Toeplitz operator with a negative-winding symbol the finite
section carries exactly `|winding|` zero singular values (Fredholm index
mechanism; control C2 confirms the sign convention: +1 winding gives kernel
{0}). The counts match `|W(L)|` to 0.2%, and `|W(L)| ~ 2 L log L` DIVERGES
as `L -> infinity`. Within the discretized wrapped model the carrier kernel
is therefore not an artifact — it is the index, and the index is unbounded
in the domain size. This makes **C0a (carrier triviality) empirically dead:
the committed archimedean model has (at truncation level) a huge kernel** —
but by the registered rule this is NOT yet an official probe verdict, and
the non-periodic line problem is governed by the same classical theory
(Hartmann-Juschenyak-Seip, arXiv:1511.08326, section on winding criteria;
Hedenmalm-Nikolaev for the meromorphic-inner case).

## 3. What this does and does not change

- The 1332 outcome table's first row (`W = {0}`) is empirically excluded but
  stays OPEN until the corrected-statistic probe (next record) rules it
  closed by a pre-registered band.
- C0b (corridor capacity, the `hcolumn` life-or-death) now has a concrete
  target: the near-kernel sector of dimension `~ |W(L)|` either hides its
  `2 + 2cos` mass in every prime-log corridor (capacity supports hcolumn)
  or does not (capacity falsifies hcolumn). This is directly measurable
  from the SVD subspace: the corridor-energy of the near-kernel projector
  `Pi_eps` is `A_tau = (1/r) * integral (2+2cos(2 pi tau xi)) K_eps(xi) dxi`
  with `K_eps` its kernel diagonal; a generic span gives `A_tau ~ 2`,
  while hiding requires `A_tau -> 0` for EVERY prime simultaneously.
- Records 1329-1331 are untouched; the 1330 brick stands. The radial leg
  remains conditional; what changed is that the conditional premise now has
  a falsification instrument pointed directly at it.

RH is not claimed.
