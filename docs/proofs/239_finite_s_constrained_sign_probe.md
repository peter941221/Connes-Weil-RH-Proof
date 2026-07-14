# Proof 239: finite-S constrained sign probe

Date: 2026-07-14

Status: rejection-first numerical diagnostic.  Raw finite sections produce
positive constrained eigenvalues, but their maximizing vectors move into the
artificial root-window boundary/high-grid sector.  Fixed smooth Galerkin
subspaces remain strictly negative for both `p=2` and `p=3`.  Therefore the
probe does not reject the finite-S sign gate and supplies no proof of it.  Its
reusable result is a guard: unconstrained full-grid eigenvalues from the
Proof 224 scattering section are not route evidence.

Proof 240 subsequently enlarges only the archimedean interval and gives an
Arb-certified fixed four-mode counterexample to the row-only archimedean sign.
It does not validate this file's finite-S scattering correction, so the
finite-S judgment here remains unchanged.

## 1. Same-object diagnostic matrix

On the root log interval, the archimedean CC20 remainder is

```text
D_infinity=-2 I+K_infinity,
```

where the ordinary Haar-coordinate kernel is

```text
K_infinity(x,y)=Q(delta)(exp(|x-y|)).                 (P.1)
```

The script evaluates `(P.1)` from the project formulas
`cc20DeltaRegular`, its first two multiplicative derivatives, and the exact
continuous diagonal value.

Proof 224's finite scattering section constructs

```text
R_a-R-(E_a-E)=-(B_a-B_0).                            (P.2)
```

After the discrete root differential `L_+=d/dx+1/2`, `(P.2)` is the metric
correction `-G_a` in

```text
D_S=D_infinity-G_a.                                  (P.3)
```

The probe therefore forms

```text
D_S^(N)=-2 I+K_infinity^(N)+K_metric^(N).             (P.4)
```

It compresses `(P.4)` to the kernel of the two independent Q-root Mellin
rows

```text
M_0(xi)=0,
M_1(xi)=0.                                           (P.5)
```

The `s=1/2` row is automatic after `g=(d/dx+1/2)xi`.  The sign gate is

```text
largest constrained eigenvalue of D_S <=0,
```

equivalently the compact part in `(P.4)` has constrained eigenvalue at most
`2`.

This matrix is a diagnostic, not a certified discretization theorem.  The
near-Sonin projection is selected from a finite scattering section, and the
Sonin cutoff/high-energy limits need not commute.

## 2. Raw full-grid result

For `p=2`, root length `0.75 log(2)`, and near-Sonin tolerance `1e-10`:

```text
+-------+------------+-------------+---------------+---------------+
| cells | Sonin rank | arch max    | finite-S max  | boundary mass |
+-------+------------+-------------+---------------+---------------+
|    12 |         18 | -2.0666667  | -1.1932313    | 0.6044        |
|    16 |         31 | -2.0369253  | +1.0594236    | 0.7442        |
|    20 |         46 | -2.0234264  | -0.0192757    | 0.6026        |
|    24 |         62 | -2.0162042  | +2.3025352    | 0.7167        |
|    28 |         79 | -2.0118727  | +2.0105111    | 0.7106        |
+-------+------------+-------------+---------------+---------------+
```

The archimedean baseline is stable.  The finite-S maximum changes sign and
the metric-correction norm grows from about `3.65` to `7.63`.  More
importantly, `60%--74%` of the maximizing vector's Euclidean mass lies in the
first and last grid entries.  This is an artificial shrinking boundary layer,
not a stable root vector.

Changing the near-Sonin tolerance from `1e-8` to `1e-12` leaves the robust
`cells=24` value unchanged but does not repair the boundary concentration.
Tolerance stability alone is therefore insufficient.

## 3. Fixed smooth Galerkin test

To separate the limits, first fix the span of the lowest Dirichlet sine modes
on the root interval, impose `(P.5)` inside that fixed space, and only then
refine the scattering grid.

For the first six physical modes at `p=2`:

```text
+-------+-----------------------------+
| cells | constrained finite-S range  |
+-------+-----------------------------+
|    12 | [-5.7295909, -2.9037780]    |
|    16 | [-6.3038048, -1.7775761]    |
|    20 | [-7.0727086, -3.0164055]    |
|    24 | [-7.2798757, -2.6551407]    |
|    28 | [-7.5300335, -3.3269149]    |
+-------+-----------------------------+
```

For the first eight modes at `p=3`, root length `0.75 log(3)`:

```text
+-------+-----------------------------+
| cells | constrained finite-S range  |
+-------+-----------------------------+
|    16 | [-4.9611431, -1.2792738]    |
|    20 | [-5.2155999, -1.0229381]    |
|    24 | [-5.0086119, -0.9510346]    |
+-------+-----------------------------+
```

All fixed low-mode maxima are strictly negative.  Raising the `p=2` physical
space to ten modes gives `+0.3383` at `cells=24` but returns to `-1.6755` at
`cells=28`; it is not a stable positive direction.

## 4. Compactness consistency guard

For a genuine compact self-adjoint operator `K` and finite-rank orthogonal
projections `P_N` converging strongly to the identity,

```text
norm(K-P_N K P_N) -> 0.                               (P.6)
```

Hence an eigenvalue of `K` strictly above `2` cannot permanently escape every
fixed smooth Galerkin scale.  Once the Galerkin space approximates its
eigenvector, the compressed Rayleigh value also exceeds `2`.

Proof 234 claims that the complete continuous finite-S correction is compact.
Therefore a discretization intended to approximate that operator must obey
the qualitative behavior `(P.6)`.  The moving boundary maxima above do not.
They diagnose a nonuniform finite-section limit, not a bad eigenspace of the
continuous operator.

This argument does not prove the sign: a genuine bad eigenvector could appear
at a higher but fixed physical mode after a convergent discretization is
established.  It only rejects the present raw full-grid output as evidence.

## 5. Reproduction

Run in WSL:

```text
python3 -B docs/proofs/239_finite_s_constrained_sign_probe.py \
  --prime 2 --cells 12,16,20,24,28 --physical-modes 6

python3 -B docs/proofs/239_finite_s_constrained_sign_probe.py \
  --prime 3 --cells 16,20,24 --physical-modes 8
```

The script prints the archimedean and metric pieces separately, verifies the
two Mellin-row residuals on the maximizing vector, reports boundary and
frequency concentration, and compares the raw grid with a fixed physical
mode space.

## 6. Route judgment

```text
literal archimedean regular kernel in the probe: exact formula
nested-complement sign convention:                   matched to Proof 224
two independent Q-root Mellin rows:                   imposed
raw full-grid positive eigenvalues:                   boundary artifacts
fixed 6-8 mode p=2,p=3 death test:                    survives / negative
convergent finite-S Galerkin theorem:                 absent
finite-S sign theorem:                               open
Lean owner or route rewire:                           none
RH:                                                   unproved
```

The next useful numerical step requires a convergent discretization of the
continuous post-Q compact owner, not a larger raw scattering matrix.  The next
analytic step is stronger: identify a fixed smooth Galerkin core for the
complete owner and prove an operator-norm tail bound.  Only then can a
certified constrained eigenvalue decide the sign gate.
