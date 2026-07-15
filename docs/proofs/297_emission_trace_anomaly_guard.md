# Proof 297: Emission-grid trace-anomaly guard

Date: 2026-07-16

Status: exact infinite-dimensional counterexample to the tempting inference
that Proof 296's emission/emission weighted blocks have zero ordinary trace.
The block has the route-shaped form

```text
u(Delta)K*[W_E,K q(Delta)K*]K v(Delta),
```

its commutator is trace class, and every scalar weight commutes with `Delta`,
yet its trace is nonzero.  Finite sections hide the value at an artificial
far boundary.

This guard is not a lower bound for the CC20 source and does not prove Gate
3U or RH.  It prevents an invalid cyclic deletion of Proof 296's all-even
sector.

## 1. Result

There exist

```text
0<Gamma<I,
Delta=I-Gamma,
K* K=Gamma,

u=q=v=I,
```

and a bounded self-adjoint detector `W_E` such that

```text
[W_E,K q(Delta)K*] in S1,                            (BH.1)
```

but

```text
Tr(u K*[W_E,K q(Delta)K*]K v)
 =-i/16 !=0.                                         (BH.2)
```

Thus

```text
commuting path weights + trace-class commutator
  does not imply zero trace.                         (BH.3)
```

## 2. Infinite unilateral-shift owner

On `ell2(N)`, let `S` be the unilateral shift and put

```text
X=(S+S*)/2,
Y=(S-S*)/(2i).                                       (BH.4)
```

Both operators are bounded and self-adjoint.  If `P_0` is the first-coordinate
projection, then

```text
[X,Y]=P_0/(2i).                                      (BH.5)
```

Choose

```text
c=1/4,
M=c(Y+2I).                                           (BH.6)
```

Since `-I<=Y<=I`,

```text
1/4 I<=M<=3/4 I.                                    (BH.7)
```

Define

```text
K=M^(1/2),
Gamma=K* K=M,
Delta=I-M.                                          (BH.8)
```

Then `Delta` is also bounded between `1/4 I` and `3/4 I`.  Set

```text
W_E=X,
u(Delta)=q(Delta)=v(Delta)=I.                       (BH.9)
```

The route-shaped weighted block is

```text
T=K[X,M]K.                                          (BH.10)
```

Equation `(BH.5)` gives

```text
[X,M]=c P_0/(2i) in S1.                             (BH.11)
```

Now cyclicity is legal because the displayed commutator itself is rank one:

```text
Tr(T)
 =Tr([X,M]M)
 =c/(2i) <e_0,M e_0>.
```

The diagonal of `Y` is zero, so

```text
<e_0,M e_0>=2c.
```

Therefore

```text
Tr(T)=c^2/i=-i c^2=-i/16.                           (BH.12)
```

This has exactly the algebraic features which the naive Proof 296 trace
cancellation would use, and it contradicts that cancellation.

## 3. Where the false finite proof cycles illegally

For a generic emission block, write

```text
A=K*W_EK,
Gamma=K*K,
```

and let `u,q,v` be bounded functions of `Delta`.  Formally,

```text
u K*[W_E,KqK*]K v
 =u(AqGamma-Gamma qA)v.                              (BH.13)
```

In finite dimensions one cycles `A` in the two terms and obtains zero because
`u,q,v,Gamma` commute.  In the source space only the difference in `(BH.13)`
is known to be trace class.  The two terms need not be trace class separately,
so that cycle is not licensed.

Proof 297 realizes the resulting anomaly explicitly.  Equation `(BH.12)` is
not a failure of trace cyclicity on `S1`; it is the result of applying
finite-dimensional cyclicity before establishing separate trace-class
ownership.

## 4. Finite sections hide the anomaly

Let `S_m` be the `m`-dimensional truncated shift.  Then

```text
[X_m,Y_m]
 =(P_0-P_(m-1))/(2i).                               (BH.14)
```

With

```text
M_m=c(Y_m+2I),
K_m=M_m^(1/2),
```

the weighted trace splits as

```text
left physical boundary   =-i c^2,
artificial far boundary  =+i c^2,
finite total             =0.                        (BH.15)
```

Increasing `m` moves the positive term farther away but never removes it from
the finite trace.  The infinite unilateral shift has no far endpoint, so only
the value in `(BH.12)` remains.

This is the same boundary-pollution mechanism recorded in Proof 264's polar
trace-anomaly guard.

## 5. Consequence for Proof 296

Proof 296's operator decomposition remains exact:

```text
T_n^off
 =T_(+++)+T_(+--)+T_(-+-)+T_(--+)+T_n^partial.
```

Finite certificates happen to report traces near zero for each interior
sector.  Proof 297 forbids promoting that observation to the continuous
source.  In particular,

```text
Tr(T_(+++))=0                                        (BH.16)
```

is not available from fixed-`S` commutator trace-class membership and
functional-calculus commutation alone.

The legal hard package remains

```text
canonical response
  +T_(+++)
  +T_n^partial,                                      (BH.17)
```

with Proof 293's outer-return/Sonin generator inserted before any attempted
cycle.  A valid zero-trace theorem would need a source-specific cancellation
of the left physical anomaly against the Sonin branch, not a generic
commutator argument.

## 6. Finite certificate

`297_emission_trace_anomaly_guard_probe.py` verifies:

```text
the finite commutator identity (BH.14);
positivity bounds for M_m and Delta_m;
K_m* K_m=M_m;
the left and far boundary values in (BH.15);
zero finite total trace;
the persistent missing infinite value |c^2|=1/16.
```

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/297_emission_trace_anomaly_guard_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/297_emission_trace_anomaly_guard_probe.py --size 37
```

The two finite cohorts report:

```text
+--------------------------------------+-------------+-------------+
| diagnostic                           | size 18     | size 37     |
+--------------------------------------+-------------+-------------+
| maximum exact error                  | 2.55e-15    | 2.43e-15    |
| finite total trace                   | 8.33e-17    | 2.78e-17    |
| left physical anomaly magnitude      | 6.25e-2     | 6.25e-2     |
| artificial far anomaly magnitude     | 6.25e-2     | 6.25e-2     |
| finite-versus-infinite trace gap     | 6.25e-2     | 6.25e-2     |
+--------------------------------------+-------------+-------------+
```

The matrix certificate checks the boundary bookkeeping.  The nonzero
infinite trace is proved analytically by `(BH.4)--(BH.12)`.

## 7. Evidence and route judgment

Project evidence:

```text
Proof 264, polar similarity trace anomaly:
docs/proofs/264_causal_gram_response.md

Proof 296, weighted reflection parity:
docs/proofs/296_weighted_reflection_parity.md
```

The guard is an elementary project construction.  No external theorem is
used beyond standard trace cyclicity when one factor is trace class.

The route now reads

```text
weighted parity decomposition
  -> reject finite interior trace-zero inference (Proof 297)
  -> retain canonical + all-even + path-boundary anomaly
  -> source-specific outer/Sonin cancellation (open)
  -> uniform compact-support bound (open)
  -> Gate 3U / finite-S sign / RH (open).
```

No Lean theorem, route consumer, or public Git history is changed.

## 8. Successor: Proof 298

Proof 298 tests the remaining path package at the reciprocal survival-gap
scale.  With `epsilon=T/N`, the complete `N`-step response converges to

```text
Tr_B(N_W integral_0^T exp(-t Gamma)dt).
```

Every reflected parity filter has a generally nonzero hyperbolic profile in
this boundary layer.  Thus the fixed-horizon zero ledger cannot be summed by
positive block norms uniformly in `N`.

The correct replacement is the ordered relative heat pair

```text
Gamma_W(s)=K*exp(sW)K,
Gamma_ord(s)=(B exp(sW) B)Gamma.
```

Its first heat jet is exactly `-t Tr(N_W exp(-t Gamma))`, and its relative
determinant is Proof 266's ordered Gram determinant.  Never symmetrize the
reference to `C_B(s)^(1/2) Gamma C_B(s)^(1/2)`: finite matrices hide the same
similarity trace anomaly proved above.  See
`docs/proofs/298_relative_gram_heat_boundary_layer.md`.
