# Record 2034 - Support-radius robustness of the found gate rows: pre-registration

Date: 2026-09-27.

Status: PRE-REGISTRATION. No theorem, no interval certificate, no RH claim.

Motivation. The registered cutoff block of record 2032 fired CUTOFF-SENSITIVE on
the record-1980 owner: at every n the sign of C moves when the prime cut is
raised from `exp(s_n)` to `exp(s_n + 1)` and `exp(s_n + 2)`. Its registered
consequence (an erratum against the prime book) is not what that block can
support: the prime book `{k prime power : k <= exp(s_n)}` is a *construction*
input fixed by the support radius `s_n = 2(n+2)`, not a measured quantity. What
the block measures is the SENSITIVITY of the gate-entry signs to that input.
The P4 reading of record 2032 then found gate rows at `n >= 1`, and those rows
inherit the same question:

```text
do the found rows keep `C > 0, b > 0, det < 0` when the assumed support radius
is moved by +-1 and +-2?
```

This record registers that probe. It measures no new gate row and adds no new
owner; it re-reads the found rows under a changed support radius.

Registered family:

```text
rows      (gamma_2, N in {3,4,5}, n = 2)
          (gamma_3, N in {3,4,5}, n = 2, 3)
          plus the n = 0 control at gamma_2 and gamma_3
gamma_2   21.022039638771556
gamma_3   30.424876125859513
deltas    -1, +1, +2          (support radius 2(n+2) + delta)
grid      xi in [-25, 25], dxi = 0.02
route     direct (B) while the enlarged prime book fits the rig cap 60000;
          above that the dual-FFT route (A) is recorded and labelled
          UNCERTIFIED and never read as a sign
```

Decision rules:

```text
RADIUS-ROBUST      every found row keeps the registered pattern at delta = +1
                   and +2. -> the found rows do not depend on the prime-cut
                   convention, and ROW-FOUND is a stable reading.
RADIUS-FRAGILE     some found row loses the pattern at delta = +1 or +2.
                   -> the found rows are conditional on the exact support
                   radius; pinning the visible-prime set (R-B0) is a
                   prerequisite before ROW-FOUND is used for routing.
DELTA-NEGATIVE     reported separately: `delta = -1` truncates the prime book
                   BELOW the construction's support radius, which is
                   inadmissible by construction; the reading is recorded as a
                   sensitivity direction only.
```

Non-claims: the `delta` axis is a support-radius sensitivity axis, not a
statement about the construction's true support radius. Nothing here changes
the record-2032 registered rules or the record-2033 pairing outcome.
