# Record 2032 - Route-B full-block assault: pre-registration

Date: 2026-09-27.

Status: PRE-REGISTRATION. No theorem, no interval certificate, no RH claim.

Context. Record 2029 section 7 leaves three reopen conditions, and the Route-B
survival screen (`route/.../002_route_b_fourpoint_span/001_survival_screen.md`)
still lists R-B0 (complete owner), R-B3 (same-index tail ratio) and R-B4
(coverage) as OPEN while R-B1 is priced viable and R-B2 is cheap but
unreachable on the certified rows. This record registers the three probes that
attack every remaining block at once. They are independent; each carries its own
decision rule and its own stop point.

```text
P4  gate-row search over the registered owner family      -> R-B0 / R-B3
P5  non-vertex lambda branch on the measured rows         -> R-B2 / R-B3
P6  interval bracket for the k = 3 weighted seed mass     -> R-B1
```

Owner, consumer, premise to remove, failure criterion (fixed for all three):

```text
owner      the record-1980 known-zero under-approximation of the formal
           closed-ball source owner, at a fixed rho, N and seed
consumer   the same-owner four-point span gate of map 106 section 2
premise    an admissible n >= 1 row with C_n > 0, b_n > 0, det_n < 0 and a
           same-index tail ratio below 1 (map 106 sections 2 and 6)
failure    a reproducible obstruction on the registered parameter class, or a
           complete error budget that exceeds the available margin
```

Every reading below is an UNDERAPPROXIMATION reading on the record-1980 owner
model. Nothing here is an interval certificate for the gate moments, a
determinant theorem, or an RH claim.

## 1. P4 - gate-row search over the registered owner family

Question (record 2029 section 7, reopen condition 1): does a *changed named
hypothesis* restore the registered pattern `C > 0, b > 0, det < 0` at an
admissible `n >= 1`? The two changed axes registered here are the height
`rho.imag` and the owner cardinality `N`; the seed (scale 0.5, power 10) and the
rig support convention `s_n = 2(n+2)`, prime book `{k prime power : k <= exp(s_n)}`
are held fixed, because they are the two quantities whose convention the gate
moments inherit from the construction.

```text
rho          0.55 + i*gamma,  gamma in {14.134725141734693,
                                        21.022039638771556,
                                        30.424876125859513}
N            3, 4, 5
n            0, 1, 2, 3, 4
xi grid      [-25, 25], dxi = 0.02 (primary), 0.01 (refinement)
routes       direct (B) where the prime book fits the rig cap 60000; the
             dual-FFT route (A, record 1959) is recorded and labelled
             UNCERTIFIED above that cap, never read as a sign
```

`rho` is a formal-owner hypothesis, not a source zero; the three heights are the
ones the survival screen already registered for height stress.

Decision rules:

```text
ROW-FOUND          some (gamma, N, n >= 1) row with a CERTIFIED route carries
                   C > 0, b > 0, det < 0, and its signs are stable between
                   dxi = 0.02 and dxi = 0.01 (|dev C| <= 1e-3).
                   -> R-B3 is unblocked; R-B2's price (record 2030) applies to
                      that row and the tail ratio becomes the live question.
NO-ROW-ON-FAMILY   no such row exists on the registered family.
                   -> scoped no-go for reopen condition 1 restricted to the
                      (height, owner-cardinality) axes at the fixed record-1981
                      seed and the rig support convention. It is NOT a no-go
                      for a changed seed, a changed composition shape, or a
                      changed support convention.
SIGN-MOVES         a candidate row's C sign is not stable under the dxi
                   refinement -> resolution artifact, reported as such.
```

Instrument diagnostics registered per row, so that a `NO-ROW` verdict carries a
mechanism and not only a label:

```text
arch / prime split of C, b, D
argmax location of W_n and the kernel value K at that argmax
prime-channel share of |C|
```

Cutoff-robustness block (counts as a reading on the rig's prime book, not on the
construction): for the record-1980 owner (`gamma_1`, `N = 4`), recompute the
gate rows with the prime cut enlarged from `exp(s_n)` to `exp(s_n + 1)` and
`exp(s_n + 2)`.

```text
CUTOFF-STABLE      the sign of C at every n is unchanged under both
                   enlargements -> the C < 0 reading is not a truncation
                   artifact of the registered prime book.
CUTOFF-SENSITIVE   a sign moves -> ERRATUM against the registered prime book of
                   records 1980/1981/2028, reported, never silently redefined.
```

## 2. P5 - non-vertex lambda branch

Record 2029 section 6 (and record 2030 section 3 item 3) note that on a `C < 0`
row the span gate is a downward parabola in `lambda`, so `gate(lambda) < 0` holds
*outside* its two roots even when the vertex value `det/C` is positive. Record
2029 section 7 item 2 registers that branch as a named alternative with its own
`qw(h_n) >= 0` half.

Registered test, exact arithmetic on the committed rows: compute the roots of
`gate(lambda) = C*lambda^2 - 2*b*lambda + D` for every measured row, and decide
whether any non-vertex `lambda` can satisfy the *whole* registered target.

```text
LAMBDA-ONLY-CANCELS     the branch removes the `det < 0` clause but not the
                   `C > 0` clause; since C does not depend on lambda and the
                   health screen of record 1931 forces `ICgate(g^2) > 0` for
                   every healthy detector, a `C < 0` row cannot be repaired by
                   any lambda. Verdict: the branch is blocked on the health
                   premise, not on the tail.
LAMBDA-SURVIVES         some row has `C > 0` and a non-vertex lambda with
                   `gate(lambda) < 0` and a tail ratio below 1.
                   -> a new witness target, to be registered on its own.
```

This probe is pure post-processing of already committed artifacts; it measures
nothing new.

## 3. P6 - interval bracket for the k = 3 weighted seed mass

Record 2031 prices R-B1 with the sharp mass `W_3` computed in 40-digit floating
point and states its own gap: "No interval certificate". The registered object is
the exact sign-piece representation

```text
A_k(a) = integral_0^1 e^{a u} |T^(k)(u)| du,
T(u)   = 1 / (1 + exp(1/u - 1/(1-u)))          (Mathlib smoothTransition),
W_k(a) = e^(-2a) A_k(a) + e^(2a) A_k(-a),
```

and on a panel on which `T^(k)` has constant sign, `integral |T^(k)|` is exact:

```text
integral_p^q |T^(3)| du = |T''(q) - T''(p)|.
```

Registered instrument: interval arithmetic (mpmath.iv, directed rounding) for
the sign-piece brackets of `T'''`, and for the upper bound

```text
A_3(a) <= sum_j exp(a * q_j) * sup |T''(q_j) - T''(p_j)|,
```

one panel per sign piece, with the panel endpoints carried as intervals. The
binding `|a|` values are 0.025, 0.225, 0.275 and 0.525 (record 2031 section 3).

Decision rule:

```text
MASS-BRACKETED   a two-sided or one-sided rigorous bracket is produced for
                 W_3 at the binding |a|, and the R-B1 strip bound recomputed
                 with the bracket's UPPER end keeps a margin below q = 2^-14.
MASS-LOST        the rigorous upper bound exceeds q -> R-B1 is not viable at
                 the registered T = 28, q and k = 3.
```

Uniformity caveat, registered up front: the record-2031 sigma-sup is a 0.01 grid
on [0,1] and its t-scan a 0.5 grid on [28,200] plus point checks. P6 does not
certify those; it certifies the one-dimensional mass only, which is exactly the
part record 2031 flagged as plausible.

## 4. What none of these can decide

- No formal-owner statement: the source-zero set is a known-zero
  under-approximation.
- No interval certificate for the gate moments `C, b, D`; floats generate data.
- No COVER statement and no TAIL Lean object.
- No RH claim.
