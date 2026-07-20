# Proof 412: Gate 3U or direct-RH route decision

Date: 2026-07-19

Status: source-backed route decision, not a proof of Gate 3U or RH.  The
shortest route from the repository's current state is still Gate 3U, but only
through the exact causal relative determinant.  The symmetric Burnol moment
quadrature, generic Toeplitz/Szego estimates, and a restart through a spectral
approximant limit are rejected as primary routes.

## 1. Decision first

```text
+------------------------------------+--------------------------+----------------------+
| route                              | missing theorem          | decision             |
+------------------------------------+--------------------------+----------------------+
| causal Gate 3U relative determinant| one uniform signed bound | continue             |
| Burnol symmetric moment quadrature | positive full metric     | diagnostic only      |
| generic BOGC / Wiener--Hopf        | source assumptions fail  | reject as import     |
| zeta spectral-triple convergence   | global compact limit     | not a shortcut       |
| Suzuki screw-function limit        | conjectural RH limit     | independent side lane|
| finite Guinand--Weil matrices      | all-window positivity    | certificate only     |
| direct proof of RH                 | RH itself                | no known shortcut    |
+------------------------------------+--------------------------+----------------------+
```

The single recommended analytic target is

```text
sup_(finite S) |partial_s log tau_S(0)|
 <=C (1+B_root)^d
      ||eta||_(H^r) ||xi||_(H^r),                    (RD.1)
```

where `tau_S` is Proof 266's fixed-`S` relative determinant built from the
positive causal Gram operator, and the derivative is the complete
outer/second-support/prolate response.  Equation `(RD.1)` is Gate 3U in its
lowest scale-invariant form.

## 2. Exact owner to retain

Use the normalized one-sided Euler inverse

```text
A_S=product_(p in S)
  (1-p^(-1/2))(I-p^(-1/2)U_(log p))^(-1).
```

On the source band `B=E-R`, put

```text
K_S=E A_S B,
Gamma_S=K_S* K_S,
W=C_xi* C_eta.
```

The response is

```text
q_S(W)
 =Tr_B(K_S* W K_S Gamma_S^(-1)-B W B)
 =partial_s log tau_S(s)|_(s=0).                    (RD.2)
```

Centering before inversion gives Proof 266's complete reward

```text
N_W=O_W+S_W+P_W,                                     (RD.3)

O_W=-B A_S* C[W,E]E A_S B,
S_W= B(I-Q)[W,Q]R A_S*E A_S B,
P_W= B Q W R A_S*E A_S B.
```

The three terms in `(RD.3)` must remain together through the common
`Gamma_S^(-1)`.  Proof 258 already rejects a separate bound for the
second-support and prolate terms.

This owner also fixes Proof 411's numerical problem.  `Gamma_S=K_S*K_S` is
positive by construction; it never requires fixed-order quadrature of cosine
frequencies `2*pi*exp(abs(z))` before inversion.

## 3. The one new theorem that would close Gate 3U

The normalized inverse has the exact probability representation

```text
A_S=E_omega[U_(X_S(omega))],

X_S=sum_(p in S) N_p log(p),
P(N_p=n)=(1-p^(-1/2))p^(-n/2).                       (RD.4)
```

Its Stinespring dilation has four conservative channels: random prime
innovation, escape across the outer boundary, the Sonin channel, and the
source band.  Proof 413 corrects the original stopping formulation below.
The missing theorem has three inseparable clauses.

```text
Signed causal determinant theorem

1. Determinant-to-dilation:
   express `(RD.2)` as one pairing of the complete reward `(RD.3)`
   with the conservative channels.

2. Common-history quotient:
   form the completed outer-minus-Sonin scalar first, quotient simultaneous
   translation of the two histories, and only then apply
   `supp(xi^star*eta) subset [-2B_root,2B_root]` to their relative
   displacement.  Large comparable-prime out-and-back paths remain and must
   cancel in the complete signed scalar.

3. Signed scalar resummation:
   retain the complete-prime telescope, every renewal level, and the
   reflected-second-support/prolate pair through one scalar cocycle; prove
   the polynomial projective root bound `(RD.1)` before the first absolute
   value.                                                           (RD.5)
```

Generic probability concentration is insufficient.  Proof 254 constructs a
shorted two-state Markov model for which the ambient boundary average is
uniform but the compressed response is nonzero.  The signed scalar
cancellation must use the actual CC20 outer, reflected, and prolate geometry.

Likewise, a raw martingale square function is insufficient.  Proof 273 proves
that compact support can kill the scalar trace of a completed crossing while
its nuclear and one-column `H1` mass stay strictly positive.  Proof 348 proves
that a short cluster of prime-log crossings has coherent root-smoothed
Hilbert--Schmidt energy at least `c X/log X`, while its diagonal Szego energy
is `O(1)`.  The nonlinear Gram normalization and all three physical branches
must act before any positive majorant.

Proof 413 makes the stopping correction decisive.  In the outer half-line
channel, simultaneous translation of two histories leaves the centered atom
unchanged once their common history has canceled.  A rule based on their
absolute positions would eventually delete a nonzero invariant scalar.  Only
the relative displacement can be clipped, and only after the completed trace
has been formed.

## 4. Why the available determinant theorems do not prove `(RD.1)`

### 4.1 Continuous Wiener--Hopf

Basor--Chen require a bounded symbol `F in L1`, an inverse Fourier kernel
`K in L1` with

```text
integral |x| |K(x)| dx < infinity,
```

and a nonvanishing index-zero factorization.  The prime-log Euler kernel is an
atomic measure, so it is outside the theorem's contract.

Source:
`https://arxiv.org/abs/math/0202062`.

### 4.2 Model-space BOGC

Bottcher's Theorem 1.1 concerns a finite Blaschke model space and symbols in
the Wiener/Krein class with canonical Wiener--Hopf factorizations.  Burnol's
actual source carrier is the weighted range `g_0 K_Theta`; its compressed
forms are `A_Theta(a |g_0|^2)`, not the unweighted truncated Toeplitz form.

Source:
`https://arxiv.org/abs/1307.0329`.

### 4.3 Tilted BOGC

Petrov's 2026 oblique identity has the right determinant architecture, but it
starts from

```text
A=I-K,  K in S1.
```

The ambient almost-periodic Euler convolution is not identity plus trace
class.  The paper's finite-dimensional differential closure is itself
Conjecture 5.12.  Its algebra may be adapted only after the repository's
relative `S1` object has been formed; it supplies no uniform estimate.

Source:
`https://arxiv.org/abs/2605.24976`.

## 5. Primary-source audit of the direct-RH alternatives

### 5.1 CCM24 semilocal prolate route

CCM24 proves Sonin transport and semilocal Hilbert-space structure.  Its
introduction says these tools are expected to open a way to semilocal Weil
positivity, and it leaves a second semilocal prolate candidate to forthcoming
work.  It does not state the finite-`S` sign or `(RD.1)`.

Source:
`https://arxiv.org/html/2310.18423v2`.

### 5.2 Zeta spectral triples

The 2025 paper gives self-adjoint finite approximants with striking numerical
zero agreement.  Section 8 explicitly names two missing steps: the
simple-even ground state and a sufficiently accurate prolate approximation
that implies convergence of the entire functions to `Xi`.  A proof of that
compact convergence would prove RH; it is not supplied.

Source:
`https://arxiv.org/html/2511.22755`.

### 5.3 Screw-function formulation

Suzuki's June 2026 paper is the strongest new alternative.  It proves:

```text
the localized Weil operator is an explicit Friedrichs extension;
its lowest eigenvalue lambda_a is continuous in a;
for sufficiently small a, lambda_a is positive and simple with an even
ground state;
for every a and lambda<lambda_a, a self-adjoint extension produces an
entire function W(a,theta;z) whose zeros are all real.
```

The RH step remains conditional.  Corollary 1.6 says RH follows if normalized
`W(a,theta(a);z)` converges uniformly on compact sets to

```text
z^2 Xi(z)/Xi'(z).                                      (RD.6)
```

The paper calls this a conjectural limit.  Its Section 7 motivation works
under `A_a>0`, the positivity whose validity for every `a` is equivalent to
RH.  Thus `(RD.6)` is a valuable independent formulation, but proving it is
not a shortcut around the global positivity problem.

Source:
`https://arxiv.org/html/2606.09096`.

The same paper gives another exact equivalent target: by continuity and
small-`a` positivity, RH is equivalent to `lambda_a` never crossing zero.
Proving

```text
ker(A_a)={0} for every a>0                            (RD.7)
```

would bypass Gate 3U, but `(RD.7)` is already an RH-equivalent global
nondegeneracy theorem with no known producer.

### 5.4 Finite Guinand--Weil dictionary

The July 2026 paper gives exact finite zero-sum coordinates and a positive
archimedean tail budget.  It explicitly states that the dictionary is one-way
and that the paper does not prove RH, Weil positivity, a prime-location bound,
or a factoring theorem.  It certifies a fixed finite matrix; it does not prove
positivity uniformly in the support window and Galerkin dimension.

Source:
`https://arxiv.org/html/2607.02828`.

### 5.5 Current external status

The Clay Mathematics Institute still lists RH as unsolved.  Connes's February
2026 survey states that semilocal positivity is equivalent to RH and that the
observed spectral convergence has not been proved.

Sources:

```text
https://www.claymath.org/millennium/riemann-hypothesis/
https://arxiv.org/html/2602.04022
```

## 6. Execution order

Do not spend the next batch on another global numerical approximation.  The
correct sequence is:

```text
412A  build the exact causal positive Burnol/CC20 Gram readback;

412B  derive the determinant-to-four-channel identity with the complete
      reward `(RD.3)`;

412C  quotient common translation history and construct the exact signed
      relative-displacement functional of Proof 413;

412D  prove the complete signed scalar-cocycle bound in the projective root
      norm, without a positive stopped square function, and instantiate
      `(RD.1)`;

412E  formalize the analytic theorem in Lean and reconnect the finite-S sign
      route.
```

Proof 413 resolves the old `412C` kill test negatively: absolute paths do not
stop, and comparable-prime returns do not vanish individually.  This kills
the stopped-martingale implementation, not the causal relative determinant.
The surviving Gate route is the complete signed scalar functional in Proof
413 `(SD.16)/(SD.19)`.  Suzuki's nondegeneracy target `(RD.7)` remains an
independent RH-equivalent lane rather than an automatic replacement.

## 7. Final judgment

```text
Can Gate 3U be closed by an existing theorem?  No.
Can current literature bypass it and prove RH?  No.
Is direct RH shorter from this repository?       No; it discards the closed
                                                  carrier/legality layers and
                                                  replaces one uniform bound
                                                  by an RH-equivalent limit.
What should be done next?                         Prove the complete signed
                                                  relative-displacement
                                                  functional bound `(RD.1)`;
                                                  pathwise stopping is false.
```

This is the one-hammer answer: continue Gate 3U, but only on the causal
three-branch relative determinant and only after common-history scalar
reduction.  Do not restart through generic Toeplitz theory, a positive stopped
square function, or a conjectural spectral limit.

## 8. Successor correction

Proof 413 supplies the analytic correction to this route decision:

```text
docs/proofs/413_relative_displacement_scalar_owner.md
```

It proves that absolute path stopping contradicts the exact half-line
common-translation identity, and that a positive stopped `H1`/nuclear column
cannot inherit compact-support scalar cancellation.  It replaces the old
kill test by the uniform projective root-functional bound `(SD.16)`, or
equivalently the complete signed local cocycle `(SD.19)`.  That estimate,
Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.
