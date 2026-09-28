# 2123 — Route B n=6 gate/tail reopening outcome

Date: 2026-09-28.

Status: GO-CANDIDATE on the registered under-approximate owner; prime-channel
certificate and formal-owner promotion remain OPEN. No producer theorem and no
RH conclusion are claimed.

## Result

The follow-up to record 2033 extends the same owner and same powered seed from
`n = 0..4` to `n = 5..7`. At `n = 6`, both registered grids produce the full
joint pattern:

```text
owner:       rho = 0.55 + 30.424876125859513 i, N = 4
owner size:  40 nodes, including 32 known zeros
support:     16
prime book:  595877 prime powers
q:           2^-14

dxi=0.02:    C =  1.1704726531961563e6
             b =  1.2168697567564184e10
             det = -5.1064396023729996e19
             tail proxy = 2.4050792126889342e-17

dxi=0.01:    C =  1.1704167580451448e6
             b =  1.2160132274965559e10
             det = -5.095160945631016e19
             tail proxy = 2.408207751770637e-17
```

The sign pattern is stable on both grids. Relative primary/fine drift is
`4.78e-5` for `C`, `7.03e-4` for `b`, `9.35e-4` for `D`, and `2.21e-3` for
the determinant. The measured gate/tail intersection is therefore real on
this numerical owner and is not the old `n=0..4` mismatch.

## What changed

Record 2035 stated that no gate row survived at `n >= 4`. That statement was
true only for the registered `n <= 4` search. Record 2123 changes the named
hypothesis by extending the index range and finds a joint row at `n=6`.
The old scoped no-go is retired only in that narrow sense.

## Remaining blocker

The `n=6` visible-prime book is `595877`:

```text
Ap certified capacity:       4000       FAILS
B certified capacity:       60000      FAILS
A registered capacity:      3000000    NUMERIC CAP ONLY
```

Thus the gate/tail pair is a genuine candidate, but it still needs a
Route-A prime-channel enclosure at the same support radius and a promotion
from the 40-node known-zero under-approximation to the formal owner. Until
those are proved, this is not a producer Go.

## Reproducibility

```text
python3 scripts/fourpoint_n6_reopen_2123.py --probe
```

Artifact: `results/2123_route_b_n6_reopen.json`.
