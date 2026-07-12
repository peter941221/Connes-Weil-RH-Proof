# Graded Lindblad Supertrace Rejection

Date: 2026-07-12

Status: the minimal graded extension of the arithmetic Lindblad route cancels
the forced diagonal exactly, but the surviving prime operator is necessarily
indefinite. The construction reproduces the original prime part of the Weil
form and supplies no lower positivity mechanism. No Lean owner is authorized.

## 1. Route Obligation

```text
route obligation:
  cancel the forced 2w identity term while retaining
  -w(U_b+U_b*) as a positive quantum energy

old weak path:
  ||sqrt(w)(U_b-I)h||^2
    = 2w||h||^2 - w<h,(U_b+U_b*)h>

new proposed owner:
  a Z/2-graded pair of positive jump channels and their supertrace

forbidden circular input:
  positivity of the complete Weil form or absence of odd harmonic states

smallest verification:
  one translation U_b and one positive weight w
```

## 2. Exact Minimal Grading

Take

```text
J_even = sqrt(w/2)(U_b-I),
J_odd  = sqrt(w/2)(U_b+I).
```

Both ordinary channel energies are positive. Their coefficient Gram matrices
in the basis `(I,U_b)` are

```text
G_even = (w/2) [[ 1,-1],[-1, 1]],
G_odd  = (w/2) [[ 1, 1],[ 1, 1]].
```

Their difference is

```text
G_super = G_even-G_odd = [[0,-w],[-w,0]],
```

so the graded energy is exactly

```text
||J_even h||^2-||J_odd h||^2
  = -w <h,(U_b+U_b*)h>.
```

The desired diagonal cancellation is therefore algebraically possible. It is
not a positivity result.

## 3. General Local No-Go

Let arbitrary even and odd jump families be linear combinations of `I` and
`U_b`. The difference of their positive coefficient Gram matrices is a
Hermitian matrix

```text
H = [[a,c],[conj(c),b]].
```

The corresponding translation operator is

```text
A_H = (a+b)I + c U_b + conj(c) U_b*.
```

Cancelling the forced diagonal means `a+b=0`. Retaining a prime atom means
`c != 0`. Under the Fourier transform, `U_b` is multiplication by a phase, so
the symbol of `A_H` ranges over

```text
2 Re(c exp(i theta)) in [-2|c|,+2|c|].
```

Thus every nontrivial diagonal-free local grading has both positive and
negative spectrum. Environment multiplicity and non-orthogonal channels only
change the two positive Gram matrices whose difference is `H`; they do not
alter this conclusion.

For finitely many translations the same argument gives a real trigonometric
polynomial with zero constant coefficient. Its circle average is zero. If it
is nonzero, continuity forces both signs. Equivalently, a finite cyclic model
is a nonzero Hermitian matrix with zero diagonal and zero trace; it cannot be
positive semidefinite.

The route's three evaluation constraints form only a finite-codimensional
subspace. Compressing a multiplication operator to a finite-codimensional
subspace does not remove either side of its essential spectrum. Hence those
constraints cannot make the graded prime operator positive.

## 4. Reproducible Probe

Run in WSL2:

```text
python3 -B docs/proofs/049_graded_prime_supertrace_probe.py
```

The local modes give

```text
+----------+-------------+-------------+-------------+
| theta    | even energy | odd energy  | supertrace  |
+----------+-------------+-------------+-------------+
| 0        | 0           | 2           | -2          |
| pi/2     | 1           | 1           | 0           |
| pi       | 2           | 0           | +2          |
+----------+-------------+-------------+-------------+
```

For the default 127-point cyclic model with weighted shifts
`(1,1),(0.7,5),(0.4,17)`, the computed spectrum is

```text
minimum = -4.2
maximum = +4.11899198016191
trace   = 3.10e-14
```

The trace residual is floating-point roundoff; the exact cyclic trace is zero.

## 5. Relation To Earlier Supertrace Guards

This is the Lindblad-channel analogue of two earlier failures:

```text
+----------------------+-----------------------------------------------+
| construction         | failure                                       |
+----------------------+-----------------------------------------------+
| Euler inner grading  | defect projection difference has eigenvalues  |
|                      | +p^(-1/2), -p^(-1/2)                           |
| equivariant complex  | exact/coexact sectors cancel completely       |
| graded Lindblad pair | prime atom survives but changes sign           |
+----------------------+-----------------------------------------------+
```

Adding the pole and archimedean terms recovers the complete coupled Weil form.
A positive factorization of that complete operator would prove the missing
Weil positivity, but the grading itself gives no such factorization. Treating
the physical space as only the positive spectral sector would store the
desired sign in the definition of the state space.

## 6. Verdict

```text
diagonal cancellation: passed exactly
prime coefficient read-off: passed exactly
ordinary Hilbert positivity: rejected by two-sided spectrum
positive cohomological quotient: not produced
new lower RH producer: none
unconditional RH: unproved
```

Related project evidence:

```text
docs/proofs/019_adelic_cech_hodge_h2_verdict.md
docs/proofs/027_pre_cutoff_euler_dilation_escape.md
docs/proofs/045_quantum_lindblad_graph_rejection.md
```
