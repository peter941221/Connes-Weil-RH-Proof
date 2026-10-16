# Quantitative interpolation and joint budget

Status: source-anchored paper derivation, not a kernel-checked new theorem,
certified numerical owner, family reopening, or RH proof.
Budget: one source-only pass, no fresh gate integration or generated modules.
Owner: the exact compact-window base and correction used by selectedOwner.
Target: replace opaque decay-constant existence by an explicit norm ledger,
then compare its cost with the same-owner gate. Stop if the ledger inputs
cannot be supplied for the complete source-zero prefix.

## 1. Explicit decay ledger

Use the source convention, not a guessed Fourier normalization:
`CC20YoshidaTail.mellinLogSliceRaw g sigma u = exp(-sigma*u)*g(exp(-u))`.
Write `h(u)=g(exp(-u))`; let its support lie in `[a,b]`, with finite real
endpoints. Let `M_j = integral |h^(j)(u)| du`, and
`E = exp(max(0,-a))`. Here j denotes ordinary derivatives in the log variable,
not derivatives in the original positive variable. For `0<=sigma<=1`, the
Leibniz rule and triangle inequality give

```text
integral |(exp(-sigma*u)*h(u))^(k)| du
    <= E * sum_{j=0}^k binomial(k,j) M_j.

C2_bound = 4 E (3 M_0 + 3 M_1 + M_2)
C4_bound = 16 E (5 M_0 + 10 M_1 + 10 M_2 + 5 M_3 + M_4).
```

These constants match the existing Fourier integral bounds at
`CC20YoshidaTail.lean:231` and `:255`: multiply by 4 or 16 and sum derivative
orders zero through two or four. They bound the normalized quantities
`|t/(2*pi)|^2 |Mellin(g)(sigma+i*t)|` and its fourth-order counterpart.
The binomial coefficients above sum the Leibniz coefficients over those
orders. No sampled maximum is used. Replacing the M_j by rigorously certified
upper bounds preserves these inequalities.

For a finite linear combination `h=sum_l c_l h_l`, triangle inequality gives
`M_j <= sum_l |c_l| M_{l,j}`. This applies to the exact finite combination
in `fixed_window_finite_mellin_surjective` at
`CC20YoshidaNearZeros.lean:1163`, but that proof obtains its combination by
span membership; it supplies neither numerical coefficients nor their bounds.

To make this ledger computable for a chosen construction, select N smooth
window-supported functions whose evaluation columns form an invertible square
matrix A on the N distinct nodes. Define exact coefficients `c=A^-1*y`, where
y is the required target-value vector. Then

```text
|c_l| <= sum_i |(A^-1)_{li}| |y_i|
       = sum_i |cofactor_{i,l}(A)| |y_i| / |det(A)|.
```

An interval-certified inverse/residual bound may replace cofactors in actual
computation. A positive lower bound for |det(A)|, or an equivalent inverse
bound, is essential. Arbitrary chosen functions need not give invertible A;
the span theorem proves a suitable finite basis exists but does not price it.
This is a construction satisfying the same interpolation requirements, not
an assertion that it equals a previously selected existential witness or
the numerical cardinal interpolant of record 1980. All gate quantities must
be recomputed/proved for whichever exact construction is used.

## 2. An explicit interpolation construction without a numerical inverse

Sign convention: the actual project `laplaceAt f z` integrates
`exp(z*x)*f.test(x)`, whereas the Fourier slice below uses `exp(-z*u)*h(u)`.
They describe the same owner only with `f.test(x)=h(-x)`, or u=-x.
The chosen symmetric seed window is inside both permitted reflected windows.
In the x coordinate the differential operator is P_i(-D_x), not P_i(D_x).
Reflection preserves all derivative L1 norms. This mapping is essential;
the unreflected polynomial must not be applied directly to the source owner.

The preceding inverse ledger can be replaced by a differential cardinal
construction, the same broad method used numerically in record 1980, but
with an analytic seed-nonvanishing guarantee. This does not identify its
owner with any stored numerical example.

Let z_1,...,z_N be the COMPLETE finite set of distinct raw interpolation nodes,
and y_i their exact targets. Choose a fixed nonnegative smooth function phi
supported inside (-1,1) with integral one. Choose r>0 so [-r,r] lies in the
allowed log window and `r*max_i |z_i| <= log(3/2)`. Set
`eta(u)=phi(u/r)/r`, `H(z)=integral exp(-z*u) eta(u) du`.
Then `|H(z_i)-1| <= exp(r*|z_i|)-1 <= 1/2`, hence `|H(z_i)|>=1/2`.
For N>=1, define

```text
P_i(X) = product_{j != i} (X-z_j)
delta_i = product_{j != i} |z_i-z_j| > 0
h = sum_i [y_i / (H(z_i)*P_i(z_i))] * P_i(D) eta
```

D denotes differentiation in u. Integration by parts has no boundary terms,
so `Laplace(D eta)(z)=z*H(z)`. Thus this h has exactly F(z_i)=y_i and
retains the compact support. No extra source zero has been omitted.

Write `P_i(X)=sum_l p_{i,l} X^l`, and
`B_k=integral |phi^(k)(u)| du`. An explicit finite bound is

```text
M_k <= 2 * sum_i (|y_i|/delta_i)
                  * sum_{l=0}^{N-1} |p_{i,l}| * r^(-k-l) * B_{k+l}.
```

Each coefficient magnitude may itself be bounded by the corresponding
elementary symmetric sum of the numbers |z_j| for j!=i. The formula gives
parameter dependence on the complete node list, separations, chosen window
and seed derivative norms, instead of an unexplained existence constant.
For N=0 choose h=0. A seed with certified B_k bounds and certified node data
would make this a numerically priced certificate; those inputs are NOT
supplied in this round. For C2 the largest required seed derivative is N+1;
for C4 it is N+3. Thus this avoids compiling one module per entry, but it
can produce a mathematically expensive bound as N grows or nodes collide.
It is not a proof that the gate pays that cost. No kernel-checked port of
this construction is claimed.

## 3. Why near-colliding nodes cannot be ignored

Let `F(z)=integral exp(-z*u) h(u) du`, with h supported in `[a,b]`.
Set `L=max(|a|,|b|)` and keep E above. For z,w in the closed strip,
integration along their straight connecting segment gives

```text
|F(z)-F(w)| <= |z-w| * L * E * M_0.
```

If the interpolation requires F(z)=1 and F(w)=-1, then
`M_0 >= 2/(|z-w|*L*E)` when the denominator is positive. The companion
nodes `rho` and `1-conjugate(rho)` have separation
`2*|Re(rho)-1/2|`. Thus a fixed-window correction carrying these targets
cannot have a uniformly bounded M_0 as rho approaches the critical line.
For this particular positive norm ledger, `C2_bound >= 24/(|z-w|*L)`.
This is a lower bound on the LEDGER'S price, not on the optimal possible
decay constant or on the true signed tail. It is not a global no-go.
The collision phenomenon is already recorded in 1799 W4; this is its explicit
connection to the derivative-norm ledger, not a novelty claim.

## 4. Compare the cost with the same-owner gate

Retain all P1-P5 of record 2708, including the actual zero prefix, positive
multiplicity, full strip, both frequency signs and actual visible primes.
Let d=169/16 from checked geometry 2710/2711. Define

```text
W = 4*Cspec*(3/4)^s / m
J = W*d*(2*pi)^12 * (q^n*C4*C2)^2

tail: J*(1+d/lambda)^2 < 1, lambda>0
gate: D - B*lambda + C*lambda^2 <= 0.
```

The new geometry transport is checked separately; this assembled strengthened
consumer is still a paper consequence requiring the raw transform identities
and decay inputs. It is not yet compiled as a full project tail theorem.

For 0<J<1, tail requires
`lambda > d*sqrt(J)/(1-sqrt(J))`. For J>=1 it is impossible for THIS bound;
for J=0 this scalar inequality holds for every positive lambda.
On the branch C,D,B>0 with Delta=B^2-4*C*D>=0, the gate allows the closed
interval with endpoints `(B-sqrt(Delta))/(2*C)` and
`(B+sqrt(Delta))/(2*C)`. Joint acceptance holds exactly when the upper gate
endpoint strictly exceeds the tail threshold. Other coefficient signs use
the quadratic inequality directly.

Equivalently, at a fixed positive lambda with W>0, C4>0 and q^n>0:

```text
C2 < lambda / ((2*pi)^6 * q^n * C4 * sqrt(W*d) * (d+lambda)).
```

This is the affordable correction-decay budget. The derivative ledger provides
a sufficient C2 upper bound to compare with it. If that ledger exceeds the
budget, this method has not certified the owner; it does not prove the true
tail fails. At fixed n, C4 and W, even lambda tending to infinity leaves the
finite ceiling `1/((2*pi)^6*q^n*C4*sqrt(W*d))`. Lambda is additionally
restricted by the actual gate.

## 5. Exact illustrative intersection, not an RH experiment

Take the toy gate `3-4*lambda+lambda^2<=0`, so its allowed interval is [1,3].
With J=(2/(d+2))^2, the tail requires lambda>2; lambda=5/2 works.
With J=(4/(d+4))^2, the tail requires lambda>4; the intersection is empty.
These are exact algebra examples only, not values from a source zero.

## 6. Decision

The derivation supplies an explicit complete-node interpolation construction,
a sufficient decay formula and a joint acceptance test. It does NOT supply
certified complete-prefix numerical node data and seed derivative norms,
the actual Cspec/m shell input, or a certified
same-owner gate. Consequently there is no admissible reopening at present.
No repeated n scan or large build is justified. The next mathematical work
must bound the interpolation inverse together with the signed gate, or expose
a scoped obstruction for this norm-ledger construction; neither task is
replaced by assuming the other will remain favorable.

## 7. Completed storage classification and cleanup

All 69994 JSON files in the inactive old `.lake/build` were parsed: every
file was `.setup.json` with ModuleSetup keys
`dynlibs,importArts,isModule,name,options,package,plugins`; no parse failure
or other JSON occurred. Lake v4.30 source `Lake/Build/Actions.lean:54` writes
the file from ModuleSetup; `Lake/Config/Module.lean:125` defines its generated
IR path. `Lake/Build/Module.lean:877` populates transitive import artifacts,
explaining the large repeated import lists. Later builds may need to
regenerate these configurations; no zero-rebuild-cost guarantee is made.

After process/path/count/byte checks, removed only these old generated setup
files: 150192552428 logical bytes. Free WSL bytes rose from 160191471616 to
310567608320. Sources, certificates, proof objects, packages and the active
build were preserved. Inventory and receipt are
`results/2713_setup_inventory.json` and `results/2713_setup_cleanup.json`.
Windows VHDX compaction was not performed.
