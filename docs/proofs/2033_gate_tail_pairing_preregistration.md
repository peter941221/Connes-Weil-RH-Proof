# Record 2033 - Route-B gate/tail pairing and the lambda screen: pre-registration

Date: 2026-09-27.

Status: PRE-REGISTRATION. No theorem, no interval certificate, no RH claim.

Input. The P4 reading of record 2032 found admissible `n >= 1` gate rows with
the registered pattern `C > 0, b > 0, det < 0` (gamma_2 at n = 2; gamma_3 at
n = 2, 3, all three owner cardinalities). That removes the premise record 2029
used to declare R-B3 blocked ("no admissible n >= 1 gate row"), and it makes the
next question mandatory rather than optional:

```text
does the SAME n carry both halves of the minimal joint target?
  gate half   C_n > 0, b_n > 0, det_n < 0            (measured, record 2032)
  tail half   beta_s * L_n < multiplicity_rho * lambda_n^2
```

The tail half is a scalar budget on the same `n` and the same vertex
`lambda_n = b_n / C_n` (map 106 sections 2 and 6; the Lean interface is
`selectedOwner_fullOrbit_span_fourthOrderSpectralTail_of_q`, whose budget
replaces the decay factor `(1/2)^n` by `q^n`). This record registers the two
probes that decide it, both of which are closed-form evaluations on already
measured gate rows.

## P4b - gate/tail pairing

Measured object, per (rho, N, n):

```text
C4, C2   base fourth-order and correction second-order decay constants,
         computed exactly as the record-2028 decay block does:
         heights 0..200 on 401 points, sigma in {0, 1/2, 1},
         scaled = |t/(2*pi)|, C4 = sup scaled^4 * |base|,
         C2 = sup scaled^2 * |correction|; the tail budget uses the base
         fourth-order constant C4 and the CORRECTION second-order C2.
A0       (3+|rho|)^4 * (2*pi)^12 * (C4*C2)^2
tau(n)   A0 * q^(2n) * (1 + (3+|rho|)^4 / |lambda_n|)^2      [q = 2^-14]
tau_inf  A0 * q^(2n)                                        [lambda -> infinity]
```

`tau(n) < 1` is the registered tail half in the rig's units (`beta_s` and
`multiplicity_rho` are formal-owner inputs; records 1981/1982/2028 use the same
unit-threshold convention, and the same form is used for the pure-decay budget
`q -> 1/2` reported alongside as the control).

Decision rules:

```text
PAIR-FOUND        some (rho, N) has one n with the gate pattern AND tau(n) < 1.
                  -> the minimal joint target is met on the measured family
                     (still only a float reading on an under-approximate owner);
                     R-B3 is no longer the binding obstacle.
PAIR-MISMATCH     at every measured n at most one half holds.
                  -> R-B3 is the binding wall on this family; the record states
                     which half fails at which n.
HEIGHT-COST       the label reported when the failure is driven by A0 growing
                  with |rho| (both the (3+|rho|)^4 prefactor and the
                  (1+(3+|rho|)^4/|lambda|)^2 closing term).
```

## P5 - non-vertex lambda screen

The span gate is the exact parabola of
`C1FourPointSpanGateCertificate.lean`:

```text
gate(lam) = D - lam * B + lam^2 * C,      B = 2 b
```

so `gate` is a parabola in the span coefficient with `lambda`-independent
coefficients. Registered readings, exact arithmetic on the measured rows:

```text
roots of gate at lam = (B +- sqrt(B^2 - 4 C D)) / (2 C)
the sign of C and which side of the roots is gate-negative
the tail budget tau(n, lam) as a function of lam, and its lam -> infinity limit
the joint set { lam > 0 : gate(lam) < 0 and tau(n, lam) < 1 }
```

Decision rules:

```text
LAMBDA-CANNOT-PAY  the joint set is empty at every measured (rho, N, n) even at
                   the lam -> infinity limit; and on the C < 0 rows the base
                   detector fails the health screen `ICgate(g^2) > 0` that
                   record 1931 makes a prerequisite, which no lam changes.
                   -> reopen condition 2 of record 2029 is closed on this family
                      as a consequence of the tail budget alone, not as a
                      judgement about the gate.
LAMBDA-PAYS        the joint set is nonempty at some measured row
                   -> a new witness target, registered on its own.
```

## P6 - interval bracket for the k = 3 weighted seed mass

As registered in record 2032 section 3 (object, instrument, decision rule), with
one added reading: the strip bound of record 2031 is recomputed with the
bracket's upper end at the binding `|a|` values.

## What none of these can decide

- No formal-owner statement: the source-zero set is a known-zero
  under-approximation.
- No interval certificate for the gate moments; floats generate data.
- COVER and the Lean consumers are untouched; no RH claim.
