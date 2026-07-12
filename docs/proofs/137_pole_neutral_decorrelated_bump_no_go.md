# Pole-Neutral Decorrelated Bump No-Go

Date: 2026-07-12

Status: route-level NO-GO for the shared mixed-Gram Schur owner. The proof
does not claim RH is impossible; it closes this proposed positive producer.

## Finite-prime set

Use the visible primes `S={2,3,5}`. Their distinct ratio shifts are

```text
d_23 = log(3/2),
d_35 = log(5/3),
d_25 = log(5/2).
```

The actual crossing Gram is

```text
G_ij(h)=min(log p_i,log p_j) F_h(log p_j-log p_i).
```

## Test construction

Choose four disjoint `C-infinity` bumps with radius `epsilon` and centers

```text
0.05, 0.52, 1.12, 1.75.
```

Take `epsilon` small enough that no difference of two bump supports lies in
the finite set `{+/-d_23,+/-d_35,+/-d_25}`. The total support width is greater
than `log(5)`, so all three primes are inside the carrier window.

The source pole-neutrality conditions are finite linear rows on the underlying
square-root test. Even in the conservative three-row model (mass plus the two
half-point rows), four bumps have a nonzero coefficient vector in the row
kernel. The probe `137_pole_neutral_decorrelated_bump_probe.py` constructs one
such vector numerically; analytically, this is just rank-nullity in a
four-dimensional bump span.

Because the support difference set avoids every `d_pq`, the resulting test
satisfies exactly

```text
F_h(d_23)=F_h(d_35)=F_h(d_25)=0.                       (P.1)
```

This conclusion is geometric and holds for every coefficient vector in the
bump row kernel; it is not a numerical cancellation.

## Diagonal Gram cost

Equation (P.1) makes the same-object Gram diagonal:

```text
G_pp(h)=log(p) ||h||_2^2.
```

For first-channel weights `w_p=p^(-1/2)`, the minimum Schur diagonal cost is

```text
w^T G(h)^(-1) w
  = (1/||h||_2^2) sum_(p in {2,3,5}) 1/(p log p).
```

After normalizing `||h||_2=1`,

```text
1/(2 log 2)+1/(3 log 3)+1/(5 log 5)
  = 1.149027... > 1.                                (P.2)
```

Thus no positive shared-channel Schur owner can absorb the exact three-prime
linear read-off into one archimedean graph norm on the pole-neutral test
space. The obstruction survives the exact source constraints because those
constraints remove only finitely many bump coefficients, while the support
geometry kills the mixed overlaps for every remaining vector.

## Route verdict

```text
ideal Brownian Gram discount: invalid same-object abstraction
actual mixed Gram: diagonalized by pole-neutral decorrelated bumps
Schur margin for {2,3,5}: 1.149027... > 1
shared mixed-Gram positive owner: NO-GO
Lean owner: forbidden
RH: still unproved
```

The next route must abandon positive Schur absorption of the linear prime
functional itself. Reweighting the same Gram, adding finite ancillas, or
relying on mixed-prime autocorrelation cannot reopen this owner.
