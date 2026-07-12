# Cutoff-Free Weil Matrix Cancellation Verdict

Date: 2026-07-12

Status: the finite Galerkin route has an exact and rigorously positive set of
tested matrices, but its positivity margin is produced by cancellation of
order-one pole, Gamma, and prime contributions down to at least `10^-53` in the
reproduced cases. Fixed coercivity, diagonal dominance, and separate block-norm
domination are rejected as proof mechanisms. The surviving scalar
Krein/Herglotz inequality remains RH-level. RH remains unproved.

## 1. Result First

```text
cutoff-free matrix construction: exact
tested matrix signs: rigorously positive by Arb interval LDL
smallest tested Rayleigh scale: below 4.87e-53
blockwise positivity: false on the minimum direction
uniform coarse spectral margin: rejected
new lower arithmetic sign theorem: none
```

The experiment uses the cutoff-free closed forms from the reproduction package
for arXiv:2607.02828. No finite archimedean cutoff `T` enters the matrix.

## 2. Reproduction Method

The project probe is:

```text
docs/proofs/043_cutoff_free_weil_spectrum_probe.py
```

It loads the upstream `arb_ldlt_certify.py` module, then:

```text
1. builds every matrix entry as an Arb interval;
2. certifies every LDL pivot as strictly positive;
3. diagonalizes only the high-precision Arb midpoints to select a test vector;
4. converts that vector to fixed decimal Arb intervals;
5. reevaluates its total and block Rayleigh quotients with Arb.
```

Thus the inertia and displayed Rayleigh enclosures are interval statements.
The midpoint eigenvalue and condition number are diagnostics.

Source package:

```text
https://github.com/akivag613/connes-cvs-
papers/2_guinand_weil_dictionary_tail_order/
```

Primary paper:

```text
https://arxiv.org/abs/2607.02828
```

## 3. Certified Positive Scales

The following runs all certified positive inertia. The eigenvalue column is the
high-precision midpoint diagnostic; for the two component runs below, the same
scale is independently enclosed by an Arb Rayleigh interval.

```text
+-------+----+-----------+----------------------+----------------------+
| c     | N  | dimension | lambda_min midpoint  | condition midpoint   |
+-------+----+-----------+----------------------+----------------------+
| 13    |  4 |         9 | 9.6792618605e-15     | 4.9849757858e13      |
| 13    |  8 |        17 | 7.6743925564e-23     | not recorded         |
| 13    | 16 |        33 | 8.5686274781e-35     | 3.8959064808e34      |
| 13    | 32 |        65 | 2.2589311906e-49     | 1.8212478816e49      |
| 100   |  8 |        17 | 4.3443206784e-32     | 1.3563198739e31      |
| 100   | 16 |        33 | 4.8600690151e-53     | 9.6027839611e52      |
| 100   | 32 |        65 | 1.5843315817e-87     | 3.4100384123e87      |
+-------+----+-----------+----------------------+----------------------+
```

At `(c,N)=(13,16)`, Arb gives

```text
Rayleigh(total)
  in [8.56862747807244431e-35 +/- 4.81e-54].
```

At `(c,N)=(100,16)`, Arb gives

```text
Rayleigh(total)
  in [4.86006901513410710e-53 +/- 4.44e-71].
```

These are explicit certified upper bounds on the smallest eigenvalue because
each comes from one named nonzero vector.

## 4. Block Cancellation

Use the upstream convention

```text
Q_infinity = W_02 - W_R - W_p
           = pole + Gamma + prime.
```

On the diagnostic minimum vector, the high-precision block values are:

```text
+-------+----+----------------+----------------+----------------+-------------+
| c     | N  | pole           | Gamma          | prime          | total       |
+-------+----+----------------+----------------+----------------+-------------+
| 13    |  4 | +2.2051760579  | -1.8894978022  | -0.3156782557  | 9.68e-15    |
| 13    | 16 | +1.6090057222  | -1.5209954661  | -0.0880102560  | 8.57e-35    |
| 100   |  8 | +2.8558280599  | -2.1952779201  | -0.6605501398  | 4.34e-32    |
| 100   | 16 | +2.2290180987  | -1.8993457083  | -0.3296723904  | 4.86e-53    |
+-------+----+----------------+----------------+----------------+-------------+
```

For `(13,16)` and `(100,16)`, every displayed component was also reevaluated
as an Arb interval. Their interval radii are below `5e-18`, while the total was
evaluated directly at the much higher precision shown above. The cancellation
is therefore not a finite-`T` or ordinary floating-point artifact.

## 5. Rejected Proof Shapes

The data rigorously reject any proposed bound at these scales whose retained
positive margin exceeds the certified Rayleigh upper bound. In particular, the
following coarse shapes cannot be uniform in `N` without reproducing the same
fine cancellation:

```text
Q_infinity >= delta(c) Id with a macroscopic fixed delta(c),
diagonal dominance with a fixed residual margin,
pole >= norm(Gamma)+norm(prime)+delta,
separate absolute-value bounds for Gamma and prime,
finite-T negative eigenvalues not compared with the tail budget.
```

This does not prove that the smallest eigenvalue tends to zero. It proves that
any claimed uniform margin larger than the displayed certified upper bounds is
already false at the corresponding finite level.

## 6. Surviving Mathematical Bottom

The cancellation matches the parity/rank-one structure described in the 2026
Krein/Herglotz reductions:

```text
pole-free operator
  -> one distinguished bad direction;

rank-one pole update
  -> scalar resolvent inequality deciding whether that direction crosses zero.
```

Sources:

```text
https://zenodo.org/records/20682834
https://zenodo.org/records/20694588
```

The scalar reduction is exact, but the source explicitly leaves its sign open.
Yoshida Proposition 1(1) identifies uniform odd Weil positivity with RH, so the
scalar inequality cannot be imported as lower data.

A viable B proof must instead produce a new arithmetic identity that rewrites
the order-one cancellation as an exact square, monotone event increment, or
signed Schur complement whose sign follows directly from primes and Gamma
terms. Merely estimating the three blocks separately destroys the observed
mechanism.

## 7. Route Judgment

```text
finite dictionary: retained
positive archimedean tail: retained
Arb cutoff-free matrices: positive at all tested cases
coarse block domination: rejected
fixed coercive-margin route: rejected at certified finite scales
Krein/Herglotz scalar condition: exact but RH-level/open
unconditional RH: unproved
```

No Lean route owner is authorized from these finite certificates. They are
evidence about the proof shape, not a proof for all `c,N`.
