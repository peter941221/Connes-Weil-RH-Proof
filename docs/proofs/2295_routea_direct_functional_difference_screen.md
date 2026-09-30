# 2295: Direct signed-functional difference and small-frequency moment repair

Date: 2026-09-30.

Result: the tested 24:4 and 24:6 physical interpolants do not pass the finite-
window diagnostic. This is a measured profile mismatch, not an integral
certificate, a bound on ideal-to-discrete hgap, or a global Filon no-go.

## Object and decision

Record 2294 rejected independent uniform-radius absolute propagation. This
probe changes that named hypothesis: it forms the same-grid signed difference
between a numerical composite-GL reference transform and the Filon interpolant
before integrating or taking any absolute values. The kernel, four-factor
polynomial, coefficient vectors and physical width-squared owner are shared.
The full support-derived kernel has 41136 prime powers. No producer premises
are removed by the diagnostic.

Let Qref/Qfilon denote the two sampled functional values. The script computes
`Gref(xi) - Gfilon(xi)` first, with
`G = K(xi) |P(xi)|^2 |B(xi)|^2 |C(xi)|^2`, then integrates that difference
on the same grid over both signs in [-40,40]. It does not split the error into
independent transform-radius charges and does not use abs(real(P)).

## Instrument repair before interpreting readings

The first arange grid missed exact zero by a tiny residual. The old polynomial-
moment recurrence repeatedly divided by this nearly zero frequency, producing
fake 1e113/1e208 readings. Those readings are withdrawn and never supply a
mathematical verdict.

For small alpha the repaired moment evaluator uses

`integral_-1^1 t^j exp(-i alpha t) dt = sum_k (-i alpha)^k/k! * integral t^(j+k) dt`,

where the final monomial integral is zero for odd j+k and 2/(j+k+1) otherwise.
For |alpha|<=1 the rapidly convergent series avoids singular division; larger
frequencies retain the existing recurrence. A separate test checks degrees
0..6 on both sides of the branch and at near-zero frequencies against smooth
high-precision polynomial integrals. This is a reference for the moment
formula, not an oracle for the oscillatory full owner.

The frequency grid now uses integer indices times the step, so its central
frequency is exactly zero. Steps 0.02 and 0.01 resolve the maximum visible-prime
frequency better than the rejected initial 0.5 screen. Resolution and order
agreement still do not certify a continuous integral.

## Readings

All profiles have 24 physical panels. Composite GL reference orders are 256
and 512 per panel; the following table shows the 512-node degree-4 control
and the 256-node degree-6 profile. The 256-node degree-4 rows agree at about
1e-14 relative on the signed difference.

```text
+---------+--------+---------------------+----------------------+--------------------+
| xi step | degree | sampled signed diff | sampled absolute diff| abs(signed) / 1e7  |
+---------+--------+---------------------+----------------------+--------------------+
| 0.02    | 4      | -1.95313743e16      | 4.18597743e18        | 1.95313743e9       |
| 0.01    | 4      | -1.95312399e16      | 4.24788444e18        | 1.95312399e9       |
| 0.02    | 6      |  8.10945853e15      | 3.07434271e17        | 8.10945853e8       |
| 0.01    | 6      |  8.10997332e15      | 3.12299209e17        | 8.10997332e8       |
+---------+--------+---------------------+----------------------+--------------------+
```

The reference sampled integral is about -1.67524199e12 at both grid steps.
The degree-4 interpolant instead gives about +1.95295646e16 on the finer grid.
The current low-degree interpolant therefore does not preserve even the sampled
functional sign. Grouped amplitude interpolation by itself is not enough.

The apparent transform-residual price gate in 2289/2290/2293 cannot be used as
a functional gate. Direct differences avoid the independent-radius floor but
still expose a large profile mismatch. This does not prove an analytic lower
bound for the true discrepancy; both quadrature rules remain uncertified.
Do not attach a supplier or claim a completed hgap from these readings.

## Reproduction and controls

`python3 scripts/routea_direct_functional_difference_screen_2295.py --steps 0.02,0.01`

`python3 scripts/routea_direct_functional_difference_selftest_2295.py`

Six controls cover small-frequency moments, a known constant-amplitude
transform, signed kernels with a full complex polynomial modulus, zero
identical-object differences, both grid steps, complete kernel size, and
reference-order movement. Order agreement is a diagnostic, not independent
analytic validation. The source/capture hashes are in the artifact.

## Remaining work

A new candidate must change a named profile or representation and pass this
same-functional diagnostic before expensive enclosure work. A frequency-aware
residual or an actual functional-difference certificate would be relevant;
more accurate arithmetic on the current 24:4 interpolant alone cannot repair
its sampled function mismatch. Tail-only profiles need their own test.
The infinite tail, selected-owner identification, hstrip and hgap remain open.
No producer GO or RH claim follows.

Evidence:
`scripts/routea_direct_functional_difference_screen_2295.py`,
`scripts/routea_direct_functional_difference_selftest_2295.py`,
`results/2295_direct_functional_difference_screen.json`.
