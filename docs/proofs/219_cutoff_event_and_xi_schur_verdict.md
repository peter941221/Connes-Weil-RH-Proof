# Proof 219: cutoff-event pairing and Xi-Schur verdict

Date: 2026-07-13

Status: one exact cutoff-flow shortcut is rejected, and one detector-specific
positive-Schur shortcut fails a stable numerical death test.  The first result
is an Arb interval statement.  The second is diagnostic evidence only.  No
finite-S positive owner is produced, no Lean route is changed, and RH remains
unproved.

## 1. Question being tested

Proof 218 removes the apparent purely archimedean surplus.  Two possible
escapes were still cheap enough to test:

```text
cutoff flow:
  pair each negative prime-power event with the following cutoff interval and
  prove that every net interval increment is positive semidefinite;

detector-specific Schur completion:
  hope that a canonical Xi quotient has enough mixed autocorrelation to keep
  the exact all-prime-power Riesz cost below the unit archimedean budget.
```

Neither test supplies a successor to Plan 032.

## 2. Exact cutoff-interval rejection

Let `Q_N(c)` be the cutoff-free finite Weil matrix from arXiv:2607.02828 in
the source coefficient basis.  A positive telescoping proof between
consecutive prime-power cutoffs would require

```text
Q_N(c_1)-Q_N(c_0) >= 0
```

on every sector it claims to cover.

The reproduction package constructs every entry as an Arb ball.  At `N=0`,
the only coordinate is scalar.  At `N=1`, the vector

```text
(e_-1-e_1)/sqrt(2)
```

is the exact odd-parity coordinate.  Direct Arb evaluation at 512 bits gives:

```text
+---------+--------------------------+--------------------------+
| interval| scalar increment         | odd Rayleigh increment   |
+---------+--------------------------+--------------------------+
| 2 -> 3  | -0.0610540277693744...   | -0.1307698745455364...   |
| 3 -> 4  | -0.0526243869877421...   | -0.0182428491385096...   |
| 5 -> 7  | -0.0149784478778197...   | -0.0024859606805801...   |
| 7 -> 8  | -0.0220606606240812...   | -0.0012637628006909...   |
| 8 -> 9  | -0.0055673900376256...   | -0.0010755578722142...   |
| 11 -> 13| -0.0070058800362659...   | -0.0005917596549468...   |
+---------+--------------------------+--------------------------+
```

Every displayed interval excludes zero by more than 30 decimal orders at the
reported precision.  One negative odd Rayleigh value already disproves
positive semidefiniteness on the odd sector.  Therefore the exact prime-event
rank-one law and the positive isolated archimedean tail cannot be assembled by
pairing consecutive values of the cutoff parameter.

This does not reject a nonlocal comparison involving several intervals or a
different congruence of the coefficient spaces.  It rejects the direct
interval-by-interval PSD telescope.

Primary source and reproduction owner:

```text
https://arxiv.org/abs/2607.02828
official source file anc/arb_ldlt_certify.py
verified file SHA256 02462e7f75a601ed8a5cc4d5c22064ece8088140ff45b9a21fd0295162c72039
docs/proofs/219_cutoff_event_pairing_certificate.py
```

## 3. Canonical quotient Schur screen

To test whether the canonical detector has special mixed-prime geometry, use
the removable critical-line quotient model

```text
H_gamma(t)=xi(1/2+it)/(t^2-gamma^2),
```

where `gamma=14.134725141734695...` is the first zeta-zero ordinate.  Its
normalized autocorrelation is

```text
F(b)=integral |H_gamma(t)|^2 cos(tb) dt
     / integral |H_gamma(t)|^2 dt,
F(0)=1.
```

For prime-power channels `q_i=p_i^m_i`, the exact same-square crossing Gram
has entries

```text
G_ij=min(log q_i,log q_j) F(log q_j-log q_i),
```

and the Euler-log pre-crossing weight is

```text
w_i=1/(m_i sqrt(q_i)).
```

The detector-specific Riesz-cost screen is `w^T G^-1 w`.  Including only
first-prime channels makes the first-zero model look nearly critical: the
costs for the first 1, 5, 10, and 15 primes are approximately `0.7213`,
`0.9799`, `0.9990`, and `1.0027`.  That apparent survival disappears when the
mandatory higher prime powers are restored:

```text
+-----------+----------+----------------+
| q <=      | channels | Riesz cost     |
+-----------+----------+----------------+
| 11        | 8        | 1.202546270438 |
| 25        | 14       | 1.779035381904 |
| 50        | 23       | 2.865228837928 |
| 100       | 35       | 3.992688612907 |
| 250       | 68       | 5.698625603386 |
+-----------+----------+----------------+
```

Steps `0.05`, `0.025`, and `0.0125` on `[0,70]` give the same displayed costs
to at least eleven decimal places.  The smallest Gram eigenvalue remains
positive in every run; at `q<=250` it is about `0.002714`.

This is not a theorem about a hypothetical off-line quotient.  It uses one
known critical-line quotient as a limiting shape and ordinary floating-point
linear algebra after high-precision Xi evaluation.  Its valid conclusion is
narrower: no route may cite the near-unit first-prime cost as evidence that
the canonical Xi shape absorbs the full Euler logarithm.  The `m>=2` channels
change the verdict before `q=11`.

## 4. Rational-cancellation rate guard

The proper rational orbit correction also has a two-sided support cost that
must not be dropped.  An off-line orbit at centered distance `delta` produces
rational poles on both sides of the critical line.  Their inverse transforms
live on opposite half-lines.  Truncating each tail at distance `T` gives root
error of order `exp(-delta T)`, but the combined root has physical span of
order `2T`; its convolution square therefore sees prime shifts through order
`2T`.

If `Delta` is the supremal centered real displacement of source zeros, the
prime-number error at logarithmic distance `2T` has the natural scale
`exp(2 Delta T)` up to subexponential factors.  The squared critical-line
approximation contributes `exp(-2 delta T)`.  Since `delta<=Delta`, selecting
a zero near the supremum gives no strictly decaying exponent.  The missing
term is exactly the contribution of the target zero in the explicit formula.

Thus a PNT-main subtraction does not repair Proof 106 by itself.  A valid
reopening must exhibit an additional signed cancellation of the target-zero
prime contribution; it may not count the two rational tails as one support
radius.

## 5. Route judgment

```text
adjacent cutoff-interval PSD telescope: rejected by Arb, including odd sector
first-prime canonical-Xi Schur discount: misleading without prime powers
all-prime-power Xi quotient Schur screen: above one by q<=11
rational-cancellation PNT exponent shortcut: no strict two-sided margin
new finite-S same-object producer: none
Lean owner or route rewire: none
RH: unproved
```

The active mathematical alternatives remain exactly those left by Proof 218:
a genuinely different finite-S positive owner with a new same-object post-Q
sign, or a detector-specific arithmetic identity that controls the complete
prime-power form rather than only its first-prime truncation.

## 6. Reproduction

After extracting the official arXiv source package so that
`anc/arb_ldlt_certify.py` is available:

```text
python3 -B docs/proofs/219_cutoff_event_pairing_certificate.py \
  --upstream anc/arb_ldlt_certify.py --prec 512

python3 -B docs/proofs/219_xi_quotient_prime_power_schur_probe.py \
  --zero-index 1 --limits 11,25,50,100,250 \
  --t-max 70 --step 0.025 --dps 40
```
