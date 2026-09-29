# Route A record 2196: derivative-mass upper-screen failure

## Consumer and owner

The consumer remains the healthy `CompactLog` B5 same-owner signed `qw >= 0`
margin. The candidate owner is the exact construction family used in records
2109, 2187, and 2195 (`gamma = 39.25244858548658`, `delta = 0.445`,
`scale = 0.8`).

## Method screened

For each smooth family profile, two integrations by parts give a quadratic
decay bound from its second-derivative mass. For the product of the base and
correction transforms, the screen used

```text
min(D2_base * M0_correction,
    D2_correction * M0_base) / (2*pi)^2
```

with absolute coefficient sums and 101 real-strip nodes. This is the
structural global-C route with triangle inequalities; it intentionally drops
all signed/cross-family cancellation.

## Result

The measured screen returned

```text
C_upper                 = 1.0702095624509457e8
B_upper                 = 4.2250180030615077e9
high-shell budget upper = 5.10095431140658e12
candidate margin        = 1.675397327895099e12
budget / margin         = 3.044623640301021
```

The binding strip row is `sigma = 1`; its correction second-derivative mass
is approximately `1.09535664e8`.

## Scoped verdict

`GLOBAL-C-TRIANGLE-ENCLOSURE` is a measured FAIL on this candidate: this
specific coarse enclosure cannot close `B_zm < epsilon`. It is not a global
Route-A impossibility result, because the screen is not interval-certified and
the discarded signed cancellation may be the binding improvement. The branch
is frozen until a named sharper mechanism is supplied: owner-local/direct
product difference pricing, signed cross-family enclosure, or a changed
detector construction.

## Verification

The heavy numeric probe completed through the resource wrapper with exit 0:
`results/20260929_weighted_zero_derivative_mass_screen_2196.log`.
The script records all quadrature and grid parameters and explicitly marks
the result as non-certified.
