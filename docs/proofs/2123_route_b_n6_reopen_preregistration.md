# 2123 — Route B n=6 gate/tail reopening

Date: 2026-09-28.

Status: PRE-REGISTRATION. This is a route-reopening probe, not an interval
certificate, producer theorem, or RH claim.

## Changed named hypothesis

Record 2033 only evaluated `n = 0..4`. This probe extends the same owner,
same powered seed, same support convention, and same gate formula to the
first later index where the prime book remains inside Route A's registered
capacity:

```text
owner       rho = 0.55 + 30.424876125859513 i, N = 4
seed        record-1981 powered seed, scale 0.5, power 10
n           6 (primary), with n = 5 and n = 7 controls
q           2^-14, unchanged from record 2033
grids       dxi = 0.02 and 0.01
support     2 * (n + 2)
prime route A capacity: 595877 prime powers at n = 6 < 3000000
```

The changed hypothesis is only the admissible index range. No owner,
detector, support, seed, or gate convention changes.

## Decision rules

```text
GO-CANDIDATE:
    n = 6 has C > 0, b > 0, det < 0 on both grids,
    relative drift is <= 1e-3 on C, b, and det,
    and the same-index q=2^-14 tail proxy is < 1.

NO-GO:
    the sign pattern fails on the fine grid, or the tail proxy is >= 1.

ROUTE-A-CAP:
    the row survives numerically but exceeds every certified prime route;
    it remains a candidate and needs a named prime-channel certificate.
```

The target is intentionally stronger than a single finite-grid sign. It
requires a same-owner sign pair and the same-index tail budget. The owner is
still an under-approximation of the formal closed-ball owner, so even a
GO-CANDIDATE does not close the RH route.
