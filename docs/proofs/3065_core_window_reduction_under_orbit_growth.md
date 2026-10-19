# The growing-orbit limit reduces to the base core window (record 3065)

Date: 2026-10-19.

Status: same-owner asymptotic reduction. It removes the high-frequency tail
and the contracted intermediate band for one fixed hypothetical zero. It
does not bound the remaining signed core or prove RH.

## Freeze the owner before increasing the orbit count

Fix one source nontrivial zero `rho`, the healthy base `b`, its contraction
threshold `T`, and the finite-prefix radius selected in record 3064. That
radius fixes one correction `c`, its finite quadratic strip constant, and the
finite prefix owner. The all-count assembly has the quantifier order

```text
choose b, T, prefix radius, c, C
                 |
                 `--> for every orbit count n, the same c and C apply
```

For each sufficiently large `n`, set

```text
epsilon_n = (6*pi)^2*(C+1)*2^(-n).
```

Then `(6*pi)^2*2^(-(n+1))*C < epsilon_n`, while `epsilon_n -> 0`. For large
enough `n`, the multiplicity tail budget is satisfied with the fixed
tail-start from record 3064, so neither the prefix radius nor `c` has to
change. Let `g_n` be the resulting selected owner. Its critical-line
transform factors exactly as

```text
G_n(t) = B(1/2+i*t)^(n+1) * D(1/2+i*t),
B(s) = laplaceAt(b,s),
D(s) = laplaceAt(c,s).
```

The exponent `n+1` includes the reserved base factor.

## The finite core and the contracted annulus

Let `S_n` be the actual visible-prime owner of `g_n`, and `m_(S_n)` its joint
symbol. Put

```text
T* = max(T,1,2*|Im(rho)|),
Q_core,n = (1/(2*pi))*integral_(-T)^T
              m_(S_n)(t)*|G_n(t)|^2 dt.
```

For `T <= |t| <= T*`, the base contraction gives
`|B(1/2+i*t)| <= 1/2`. Since `c` is fixed and compactly supported,

```text
M_D = sup_(|t|<=T*) |D(1/2+i*t)| < infinity.
```

The archimedean symbol bound and record 3059's same-owner prime envelope
give

```text
|m_(S_n)(t)| <= K + 18*T*^2 + 48*(n+2)*exp(n+2).
```

Thus the absolute contribution from the two annular pieces
`T <= |t| <= T*` is at most

```text
E_ann,n <= ((T*-T)/pi) * M_D^2 * 4^(-(n+1))
            * (K + 18*T*^2 + 48*(n+2)*exp(n+2)).
```

It tends to zero because its largest term is a constant times
`(n+2)*(e/4)^n`, and `e/4<1`.

## The outer tail

Record 3064 with `epsilon_n` gives the record-3058 bound

```text
E_tail,n <= A0*epsilon_n^2
  * (Q0 + 48*(n+2)*exp(n+2)),
A0 = 16/(3*pi*T*^3),
Q0 = K + 8 + log(2) + log(T*) + 1/3.
```

Since `epsilon_n^2` is a constant times `4^-n`, this is also bounded by a
constant times `(n+2)*(e/4)^n`, and tends to zero. Combining the annulus and
the outer tail yields

```text
|qw(g_n) - Q_core,n| <= E_ann,n + E_tail,n -> 0.
```

The whole-line sign problem therefore has the asymptotic form of a signed
integral on the fixed interval `[-T,T]`, with both omitted regions vanishing.

## Exact remaining obstruction

The core sequence is still owner-dependent in two ways:

```text
Q_core,n uses |B(1/2+i*t)|^(2*(n+1)),
m_(S_n) uses the growing visible-prime set S_n.
```

The detector theorem gives `qw(g_n)<0` for every `n`, so the reduction implies
only `Q_core,n <= o(1)`. It does not give a lower bound. To contradict strict
negativity at a finite index, a producer proof needs

```text
Q_core,n >= E_ann,n + E_tail,n
```

for some sufficiently large `n`, while preserving the same `S_n` and
base/correction owner. A fixed positive lower margin would suffice because
the errors tend to zero. A mere limit-infimum bound `Q_core,n >= -o(1)` does
not suffice: `qw(g_n)` could approach zero strictly from below. A lower bound
for one fixed core function cannot be substituted because the convolution
power and visible-prime owner both change with `n`.

This is narrower than the original whole-line problem: no estimate of the
far-tail positive credit is needed after the epsilon schedule, and no
uniform-in-rho interpolation constant is needed for this fixed-rho limit.
The unresolved part is now exactly the varying finite-core signed balance.

Evidence:

- `ConnesWeilRH/Source/CC20YoshidaConvolution.lean` constructs the correction
  before the convolution count and gives its all-count quadratic tail bound.
- `ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean` fixes the tail radius before the
  later orbit count.
- `docs/proofs/3064_epsilon_tunable_far_tail_price.md` makes the outer-tail
  contribution vanish under the chosen epsilon schedule.
- `docs/proofs/3059_visible-prime-symbol-envelope_price.md` bounds the
  owner-dependent symbol by the support radius.
