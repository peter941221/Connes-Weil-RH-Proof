# 2137 - Two-sided r48 tail screen and 2136 correction

Date: 2026-09-29.

Status: TWO-SIDED-NUMERICAL-SCREEN, NOT A CERTIFICATE. The one-sided reading
in record 2136 cannot be cited as a full-line tail bound.

## Consumer, owner, failure criterion

The consumer is same-owner signed C3' for the selected healthy CompactLog
detector, then SourceRH. This screen keeps the one-copy G8-H numerical owner,
scale 0.88, support 9.504 and the m=6400 coefficient path of record 2136.
It does not promote that owner to the actual closed-ball source-zero owner.
The named failure criterion was a missing tail sign or incorrect polynomial
modulus that invalidates the 2136 full-line interpretation.

## Finding

The 2136 implementation integrated only `x >= 160`, although the Weil
integral is over the full real line. Its `p` factor was `abs(real(P))`, which
is not an upper bound on `abs(P)`. Record 2137 uses the exact product
`abs(P(-2 pi i x)) = product_j hypot(Re node_j, Im node_j + 2 pi x)` and
evaluates both `x >= 160` and `x <= -160`. These are sampled integrals of
an envelope, not certified bounds on the integrals.

```text
grid nodes    positive 160..1e6     negative -1e6..-160
5000          8.09684361686766e-291 4.04325209342770e-284
10000         8.04872095382891e-291 4.01492565251276e-284
20000         8.03667568823177e-291 4.00783354211398e-284
```

At 5000 nodes the negative-side reading is about 4.99e6 times the positive
side. The two-sided sampled total is about `1.1871e-296 * |Q1600|`, but
even this ratio is not a certified tail bound. Refinement changes the
5000-node reading by about 0.88 percent on the negative side. The apparent
zero infinity remainder is float underflow, not an exact zero or proof.

## Decision

The 2136 full-line reading is withdrawn (scoped instrument no-go). The
two-sided order-48 mechanism survives this screen numerically, with huge
scale slack on the one-copy owner. A sound bound still needs (1) an
independent audit of N48 and the derivative endpoints, (2) an enclosure of
both integrals and an explicit infinity remainder, (3) an analytic bound on
the archimedean kernel over the full tail, and (4) actual-owner transfer.
Finite-window signed C3' and COVER remain untouched. Do not spend more
high-resolution quadrature time unless it discharges one of these premises.

Reproduce with `python scripts/routea_fixed_r48_tail_absP_screen_2137.py`.
Evidence: `results/2137_routea_fixed_r48_absP_screen.json`,
`scripts/routea_fixed_r48_tail_price_2136.py`, and
`scripts/fourpoint_owner_density_1959.py` (`P_from_nodes`).
