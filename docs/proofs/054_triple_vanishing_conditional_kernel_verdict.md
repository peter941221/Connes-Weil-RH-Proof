# Triple-Vanishing Conditional-Kernel Verdict

Date: 2026-07-12

Status: the exact finite Guinand--Weil dictionary can be restricted to the
same triple-vanishing square tests, and the tested restricted total matrices
are Arb-certified positive. This does not yield a lower proof: the pole block
vanishes, but the remaining Gamma and prime blocks are separately indefinite
and cancel on rapidly shrinking scales. Uniform positivity of the coupled
restricted matrices is the finite constrained Weil sign itself. No Lean owner
is authorized.

## 1. Same-Object Constraint Identification

The finite dictionary starts from an even coefficient vector
`v=(v_0,...,v_N)` and defines

```text
T_v(t) = sum_(m=-N)^N u_m exp(2 pi i m t),
K_v(omega) = 2 integral_(0..omega) T_v(t)T_v(omega-t) dt,
hat(g_v)(xi) = pi K_v(1-|xi|/Delta).
```

Under the Mellin/Fourier normalization, the CC20 points `s=0,1/2,1`
correspond to `z=+i/2,0,-i/2`. Since `g_v` is even, the two endpoint
conditions coincide.

The central condition is exactly linear in the underlying square root. Indeed,
evenness and one-periodicity give `T_v(1-t)=T_v(t)`, so the two triangles of
the unit square contribute equally and

```text
integral_0^1 K_v(omega) d omega
  = (integral_0^1 T_v(t) dt)^2
  = v_0^2.
```

Since `2 pi Delta=log(c)`, it follows that

```text
g_v(0) = log(c) v_0^2.
```

Thus `g_v(0)=0` is exactly `v_0=0`.

The source paper proves

```text
<v,Q_pole v>
  = C_c beta^2
      (v_0/beta^2
       + sqrt(2) sum_(k=1)^N v_k/(k^2+beta^2))^2
  = 2 g_v(i/2),

beta=log(c)/(4 pi), C_c>0.
```

Hence the two independent coefficient constraints are

```text
v_0 = 0,
v_0/beta^2 + sqrt(2) sum_(k=1)^N v_k/(k^2+beta^2) = 0.
```

The second also forces `g_v(-i/2)=0` by evenness. These are the finite
dictionary's exact same-object realization of the triple vanishing; the
moment-neutral row `M_0(v)=0` from the source paper is a different condition
and was not substituted for it.

## 2. Certified Compression

The probe constructs an explicit basis of the two-row kernel. It embeds that
basis into the full `{-N,...,N}` coefficient matrix and compresses the total,
pole, Gamma, and prime blocks with Arb arithmetic. It then performs interval
LDL separately on every compressed block.

```text
+------+-----+------+----------------+----------------+----------------+
| c    | N   | dim  | min total      | Gamma inertia  | prime inertia  |
+------+-----+------+----------------+----------------+----------------+
| 13   | 4   | 3    | 1.3995e-6     | (2+,1-)        | (1+,2-)        |
| 13   | 8   | 7    | 3.8635e-14    | (6+,1-)        | (3+,4-)        |
| 13   | 16  | 15   | 7.4225e-25    | (14+,1-)       | (7+,8-)        |
| 29   | 8   | 7    | 5.8358e-18    | (5+,2-)        | (3+,4-)        |
+------+-----+------+----------------+----------------+----------------+
```

The inertia statements are certified. The minimum-eigenvalue values are
high-precision midpoint diagnostics after the certified positive inertia.

The negative component scales are not small:

```text
+------+-----+----------------------+----------------------+
| c    | N   | min Gamma midpoint   | min prime midpoint   |
+------+-----+----------------------+----------------------+
| 13   | 4   | -0.2468774446        | -93.34834637         |
| 13   | 8   | -0.2488660298        | -1121.295883         |
| 13   | 16  | -0.2501272313        | -54709.01075         |
| 29   | 8   | -0.5255819366        | -1.613108977         |
+------+-----+----------------------+----------------------+
```

For every run:

```text
constraint residual: Arb zero
compressed pole block: every entry contains zero
compressed total inertia: all positive
```

## 3. What The Experiment Rejects

The triple constraints do not turn either remaining source into a positive
kernel:

```text
Gamma restricted form >= 0: false
prime restricted form >= 0: false
separate positive-measure representation: unavailable
absolute block domination with stable margin: contradicted by scale
```

The total restricted sign survives only through the coupled cancellation

```text
Q_restricted = Gamma_restricted + prime_restricted.
```

Calling this coupled sum a conditionally positive kernel merely renames the
desired statement. If the union of these finite square tests is proved
determining in the CC20 triple-vanishing class, positivity for every `c,N`
implies the finite-vanishing Weil criterion and hence RH. Without a determining
theorem, the finite statement cannot close the route.

A genuinely lower continuation would need an explicit Gram or Dirichlet-form
identity for the coupled Gamma--prime sum whose positivity follows before the
Weil zero-sum interpretation. Cholesky factors computed after positive LDL do
not qualify: they consume the sign being proved.

## 4. Reproduction

With the official arXiv:2607.02828 source package unpacked and `python-flint`
plus `mpmath` available, run:

```text
python3 -B docs/proofs/053_triple_vanishing_weil_probe.py \
  --upstream anc/arb_ldlt_certify.py \
  --component-probe docs/proofs/043_cutoff_free_weil_spectrum_probe.py \
  --c 13 --N 4 --prec 1024
```

Repeat with `(c,N,prec)=(13,8,1536)`, `(13,16,3072)`, and `(29,8,1536)`
for the remaining rows.

## 5. Verdict

```text
exact finite triple-vanishing subspace: identified
same-object constraint projection: passed
pole removal: passed exactly
restricted finite total signs: positive in tested cases
separate lower positive kernels: rejected
uniform coupled positivity as source root: forbidden / RH-level
new Lean owner: none
unconditional RH: unproved
```

Sources:

```text
https://arxiv.org/abs/2607.02828
main.tex, finite dictionary and Corollary "Pole-neutral source survival"
ConnesWeilRH/Source/CC20RHExit.lean:21-29
docs/proofs/041_finite_galerkin_escape_screen.md
```
