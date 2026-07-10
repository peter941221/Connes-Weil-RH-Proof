# Plan 012 Mathematical Verdict

Date: 2026-07-10

Decision:

```text
fixed-S Hilbert-Schmidt/operator-kernel problem: derivable
current exact no-defect read-off target: false
plan 012 status: rejected on its current theorem statement
Lean changes authorized by this verdict: none
```

## 1. Route Obligation Under Review

The active consumer asks for the exact equality

```text
supportSquareTrace = qwLambda.
```

The repository states that equality in
`ConnesWeilRH/Route/Theorem1.lean:274-278` as
`RestrictedTraceReadOffEquality`. Plan 012 proposed an operator/kernel layer
followed by rank, pole, and `Cdef` bookkeeping that would remove every trace
remainder before constructing `SourceTraceReadOffData`.

Two questions control that proposal:

```text
Q1. Does the selected compressed operator have a Hilbert-Schmidt realization?
Q2. Does its ordinary positive trace equal qwLambda with no remainder?
```

Q1 has a direct proof in the semilocal scattering coordinate. Q2 fails in the
single archimedean case, including on tests with the route's three vanishing
conditions.

## 2. Primary Sources

The proof uses these source results.

```text
Connes, Trace formula in noncommutative geometry and the zeros of the
Riemann zeta function, arXiv:math/9811068
https://arxiv.org/abs/math/9811068

Connes and Consani, Weil positivity and Trace formula, the archimedean place,
arXiv:2006.13771
https://arxiv.org/abs/2006.13771

Connes, Consani, and Moscovici, Zeta zeros and prolate wave operators,
arXiv:2310.18423v2
https://arxiv.org/abs/2310.18423
```

CCM24 constructs the unitary map

```text
V_S = M_S U_S : L2(X_S)^(K_S) -> L2(R, dm_S)
```

and proves that the semilocal Fourier transform becomes reflection
`s -> -s`. See `mainc2m24fine.tex:786-804`, Proposition 4.2. The same paper
defines `X_S`, its measure coordinate, and `w_S` at lines 700-741.

CC20 proves the exact projection identity

```text
P P_hat P = -P (1/2) u_infinity^* [H,u_infinity] P
```

and checks the trace-class step needed for cyclicity. See
`weil-compo.tex:542-559`. Its Theorem `thmqkey1` proves the nonzero remainder
formula used below at lines 765-808.

## 3. Direct Fixed-S Hilbert-Schmidt Construction

Work on the `K_S`-invariant semilocal space. Pass through `w_S`, then use the
logarithm of the module. The Hilbert space becomes

```text
H = L2(R, dx).
```

Let `P` multiply by `1_[0,infinity)`, let `J` reflect `x -> -x`, and let
`F` denote the additive Fourier transform between the log and spectral
coordinates. CCM24 Proposition 4.2 gives the fixed-S scattering phase

```text
u_S(s)
  = product_(v in S) L_v(1/2+is) / L_v(1/2-is),

abs(u_S(s)) = 1.
```

The choice of numerator and denominator follows the Fourier convention. Its
inverse gives the adjoint convention and leaves the ideal estimates unchanged.
In the log coordinate define

```text
U_S = F^(-1) M_(u_S) F.
```

The semilocal Fourier operator has the form `J U_S`. Hence

```text
P_hat_S = U_S^* (1-P) U_S.
```

For `g in C_c^infinity(R)`, let `C_g` be convolution by `g` and set

```text
A_(S,g) = P_hat_S P C_g,
T_(S,g) = (1-P) U_S P C_g.
```

Then `A_(S,g) = U_S^* T_(S,g)`. The following commutator identity proves the
Hilbert-Schmidt property:

```text
T_(S,g)
  = (1-P) [U_S,P] C_g
  = (1-P) (U_S [P,C_g] + [U_S C_g,P]).
```

For a convolution operator `C_k`, the commutator has measurable kernel

```text
K_[P,C_k](x,y)
  = (1_[0,infinity)(x) - 1_[0,infinity)(y)) k(x-y),
```

with the exact norm formula

```text
norm([P,C_k])_HS^2
  = integral_R abs(t) * abs(k(t))^2 dt.
```

Both kernels needed above satisfy that integral bound:

```text
k_0 = g,
k_1 = F^(-1)(u_S * F(g)).
```

The archimedean factor has derivatives of polynomial and logarithmic growth;
CC20 checks this at `weil-compo.tex:448-464`. Each finite Euler factor has
bounded derivatives because `1-p^(-1/2)` bounds its denominator away from
zero. Therefore `u_S F(g)` and `k_1` are Schwartz functions. We obtain

```text
norm(A_(S,g))_HS = norm(T_(S,g))_HS

  <= (integral abs(t) abs(g(t))^2 dt)^(1/2)
     + (integral abs(t) abs(k_1(t))^2 dt)^(1/2).
```

The route's finite cutoff translates the half-line boundary. Write
`P_a = 1_[a,infinity)` in the log coordinate. Reflection sends it to
`1-P_(-a)`. The same calculation gives

```text
(1-P_(-a)) U_S P_a C_g

  = (1-P_(-a)) [U_S,P_a] C_g
    + (1-P_(-a)) P_a U_S C_g.
```

The first term uses the translated commutator estimate above. The second term
has output in the finite strip between `a` and `-a`, or vanishes when those
half-lines do not overlap. For a finite strip `E`,

```text
norm(1_E C_(k_1))_HS^2 = measure(E) * norm(k_1)_L2^2.
```

This proves the Hilbert-Schmidt statement for each finite route cutoff, with
the cutoff dependence exposed by the strip length.

Every Hilbert-Schmidt operator on this sigma-finite standard `L2` space has an
`L2(R x R)` kernel. One concrete kernel construction applies `U_S` or `U_S^*`
in the first variable to the two explicit commutator kernels above. This
produces `K_A` as an `L2` equivalence class and gives

```text
Tr(A_(S,g)^* A_(S,g)) = norm(A_(S,g))_HS^2 >= 0.
```

The old Phase 0A requirement for a separate pointwise majorant exceeded the
mathematical requirement. The majorant `abs(K_A)` belongs to `L2`, and the
trace identity uses the ordinary positive trace rather than a diagonal of an
arbitrary kernel representative.

## 4. Exact Source Remainder

The same coordinate gives the fixed-S version of the CC20 algebra:

```text
P P_hat_S P = -P (1/2) U_S^* [H,U_S] P,
H = 2P-1.
```

For a test `f`, define the integrated fixed-S trace remainder in the common
coordinate by

```text
D_S(f)
  = positiveSupportSquare_S(f) - localWeilTerms_S(f).
```

The two terms use the same theta-smoothed operator and scattering phase, so
this defines a continuous source distribution rather than a free scalar. A
pointwise `delta_S(rho)` requires a separate trace-class statement for the
unsmoothed scaling operator and is not needed for the rejection. The operator
identity gives

```text
positiveSupportSquare_S(f)
  = localWeilTerms_S(f) + D_S(f),

D_S(f) = integrated fixed-S trace remainder.
```

This construction derives the fixed-S object in its unitary coordinate. It
uses no transport through the nonunitary map `eta_S`, and it creates no `M_S`
projection-order terms. The term `D_S` remains in the formula.

## 5. Counterexample To Exact No-Defect Read-Off

The archimedean case `S={infinity}` refutes the current consumer. CC20 defines
`D` at `weil-compo.tex:755-758` and proves

```text
D o Q(xi * xi^*)
  = inner(xi, (-2 Id + K_I) xi),
```

where `K_I` is Hilbert-Schmidt on `L2(sqrt(I),d*rho)`. See Theorem
`thmqkey1`, `weil-compo.tex:765-808`.

Let

```text
H_0 = {xi in L2(sqrt(I)) | integral xi d*rho = 0}.
```

`H_0` has codimension one and remains infinite-dimensional. Assume that the
quadratic form above vanishes on `H_0`. Polarization would give

```text
compression_H0(K_I) = 2 Id_H0.
```

The source kernel at `weil-compo.tex:803-806` is symmetric, so `K_I` is
self-adjoint and polarization applies. The left side is compact. The identity
on an infinite-dimensional Hilbert space is not compact. The assumption is
false. Density of compact smooth functions in `H_0` supplies

```text
xi in C_c^infinity(sqrt(I)),
integral xi d*rho = 0,
D o Q(xi * xi^*) != 0.
```

Set

```text
F = Q(xi * xi^*).
```

CC20 Lemma `vanishing1` shows that `Q` preserves support and positive
definiteness; see `weil-compo.tex:730-750`. Its Mellin transform is

```text
F_hat(t)
  = (t^2 + 1/4) * xi_hat(t) * conjugate(xi_hat(conjugate(t))).
```

Consequently

```text
F_hat(+i/2) = 0,
F_hat(-i/2) = 0,
F_hat(0) = 0
```

because `integral xi = 0`. Thus `F` satisfies the route's three vanishing
conditions, while

```text
D(F) != 0.
```

Choose `I` inside `(1/2,2)`. CC20 states that this support range contains no
finite-prime contribution; see `weil-compo.tex:114-116`. The two Tate pole
evaluations vanish for `F`. In this case the restricted Weil value is the
archimedean Weil term, but CC20 Proposition `proplittlesq` and Corollary
`corlittlesq` give

```text
positiveSupportSquare(F)
  = restrictedWeil(F) + D(F)
  != restrictedWeil(F).
```

This contradicts the current `RestrictedTraceReadOffEquality` target for the
genuine CC20 operator model.

## 6. Consequences For Plan 012

The fixed-S Hilbert-Schmidt and ordinary positive trace layers remain valid
mathematical work. They cannot construct the current no-defect consumer.

```text
operator/kernel bottom: closed by the direct commutator proof
ordinary positive trace: closed by Tr(A* A)=norm(A)_HS^2
post-Q remainder existence: closed by D_S o Q
remainder identically zero: disproved
supportSquareTrace = qwLambda: disproved for the genuine source model
two 012 Dev roots: cannot be retired by the planned analytic owner
```

A corrected route must keep `D_S` in the consumer or add a proved conditioning
theorem that controls its sign. CC20 uses finite-codimension conditioning for
that purpose. Replacing `D_S` by a zero `Cdef` field would reproduce the false
equality.

## 7. Scope Of The Rejection

This verdict rejects the theorem statement selected by plan 012. It does not
reject semilocal quantized calculus, the Connes trace formula, or the strategy
of controlling `D_S` on a conditioned subspace. It also does not prove or
disprove RH.
