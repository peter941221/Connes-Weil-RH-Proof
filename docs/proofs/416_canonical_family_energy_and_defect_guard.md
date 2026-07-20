# Proof 416: Canonical-family energy recovery and finite-defect guard

Date: 2026-07-19

Status: the selected exact-support-to-finite-`S` bridge is now an axiom-clean
Lean owner.  Analytically, the canonical cutoff restores a polynomial bound
for the complete diagonal Euler energy.  A closed-form Bernstein--Szego model
simultaneously rejects the stronger shortcut that would bound the endpoint
response from near invariance and the root commutator alone.

This proof does not bound the completed Burnol boundary form, close Gate 3U,
prove the finite-`S` sign, prove Burnol's identity, or prove RH.

## 1. Result

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| selected square constructs its own finite-S family   | Lean-owned           |
| powered family indices equal exact nonzero atoms     | both directions      |
| visible primes come from nonzero selected atoms      | Lean-owned           |
| visible prime base has selected support cutoff       | Lean-owned           |
| arbitrary finite-S global Euler energy               | divergent guard kept |
| canonical-family full Euler energy                   | O((1+B)^2)           |
| endpoint root commutator alone bounds response       | false analytically   |
| condition-number-free finite-defect shortcut         | rejected             |
| canonical Burnol energy-to-boundary estimate         | open                 |
| Gate 3U / RH                                         | open / unproved      |
+------------------------------------------------------+----------------------+
```

The corrected dependency is

```text
selected compact convolution square F
  -> exact nonzero prime-power support
  -> canonical FinitePrimePowerFamily
  -> canonical visible primes S_F
  -> full Euler square energy O((1+B_F)^2)
  -> Burnol completed boundary response.                 (CE.1)

The last arrow is the remaining theorem.  Near invariance alone does not
produce it.

## 2. Canonical-family Lean owner

The new module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCanonicalFamily.lean                        (CE.2)
```

For a selected owner, compact support already constructs

```text
SelectedFinitePrimeSupportData.ofOwner owner.             (CE.3)
```

For every supported natural index `n`, use the canonical factorization

```text
p(n)=n.minFac,
m(n)=n.factorization(n.minFac),
p(n)^m(n)=n.                                              (CE.4)
```

Mathlib's `IsPrimePow.minFac_pow_factorization_eq` proves `(CE.4)`.  The
family is the image of the exact support under `(CE.4)`; it does not choose an
independent place set or a noncanonical prime-power witness.

The main theorem is

```text
exists_mem_ofSelectedOwner_pow_eq_iff owner n:

  (exists pm in (ofSelectedOwner owner).terms,
     pm.1^pm.2=n)

  iff

  IsPrimePow n and owner.finitePrimeTerm n !=0.           (CE.5)
```

The module also proves

```text
p in (ofSelectedOwner owner).visiblePrimes
  ->exists m, owner.finitePrimeTerm(p^m)!=0,              (CE.6)

p in (ofSelectedOwner owner).visiblePrimes
  ->p<owner.globalIndexBound.                             (CE.7)
```

Thus the CCM24 semilocal carrier and the arithmetic trace family are now
derived from the same selected square.  Proof 415's exact-support constructor
obligation is closed; the analytic estimate for that family is not.

## 3. Why finite defect is not the estimate

Proofs 375--377 give a uniform Hilbert--Schmidt root-commutator bound for
every scalar nearly invariant endpoint.  It is tempting to infer that the
completed endpoint response is uniformly bounded as well.  The following
exact model disproves that inference.

Work on circle `L2`.  Let

```text
K_N=span{1,z,...,z^(N-1)},
theta=z^N,
0<r<1,
1<=M<=N.                                                (FD.1)
```

Use the bounded invertible outer multiplier

```text
m_(M,r)(z)=(1-rz)^(-M),
h_(M,r)=abs(m_(M,r))^2.                                 (FD.2)
```

Let

```text
G=P_N M_h P_N,
A=P_N M_(h z) P_N,
S_h=G^(-1)A.                                            (FD.3)
```

`S_h` is the fixed-coordinate normalized compression of multiplication by
`z` to `m_(M,r)K_N`.  Its order is the same Gram order used in Proofs 407 and
415; no polar trace cycle is made.

## 4. Exact Bernstein--Szego calculation

Define the monic polynomial

```text
Phi_N(z)=z^(N-M)(z-r)^M.                                (FD.4)
```

On the unit circle,

```text
(z-r)^M=z^M conjugate((1-rz)^M).                       (FD.5)
```

For `0<=k<N`, `(FD.2)--(FD.5)` give

```text
<Phi_N,z^k>_h

 =integral_T z^(N-k)/(1-rz)^M dm(z)
 =0.                                                    (FD.6)
```

The last equality holds because `(1-rz)^(-M)` has only nonnegative Fourier
frequencies and `N-k>=1`.  Hence `Phi_N` is the degree-`N` monic orthogonal
polynomial for the weight `h`.

The characteristic polynomial of the weighted compressed shift `(FD.3)` is
the degree-`N` monic orthogonal polynomial.  Therefore

```text
Tr(S_h)=sum of the zeros of Phi_N=M r.                  (FD.7)
```

This is the standard finite OPUC compression identity, but `(FD.4)--(FD.7)`
also give a direct proof for this family.  A general source reference is Barry
Simon's *Orthogonal Polynomials on the Unit Circle, Part 1*:

```text
https://www.ams.org/books/coll/054.1/
```

Now use the fixed positive detector

```text
C=I+M_z,
W=C* C=2I+M_z+M_z*.                                   (FD.8)
```

The unweighted shift on `K_N` has trace zero.  Rectangular cycling is legal in
this finite-rank calculation, so `(FD.7)` gives the exact response

```text
Tr[W(P_(m_(M,r)K_N)-P_N)]=2 M r.                      (FD.9)
```

The detector `(FD.8)` and its Fourier support do not depend on `M`.  Both
spaces in `(FD.9)` are scalar nearly invariant, and their shift commutators
have the uniform finite-defect bound from Proof 376.  Nevertheless `(FD.9)`
is unbounded as `M` grows.  Therefore

```text
uniform endpoint root commutator
  -X-> uniform relative endpoint trace.               (FD.10)
```

The missing quantity is the accumulated boundary cocycle encoded by the
normalized Gram.  This is the finite Bernstein--Szego version of Proof 264's
trace-anomaly guard.  It does not refute a bound which also charges the
complete Euler logarithmic energy.

## 5. Canonical support restores the full Euler energy

For a finite visible family `S`, Proof 414 records the diagonal logarithmic
Euler energy

```text
E(S)
 =sum_(p in S)sum_(m>=1) log(p)/(m p^m).              (EN.1)
```

It diverges along arbitrary growing finite prime sets, so it cannot prove the
old all-finite-`S` Gate.  The canonical family has a different quantifier.
By `(CE.6)--(CE.7)`, every visible base satisfies, up to the harmless integer
ceiling,

```text
p<=exp(B_F).                                           (EN.2)
```

For every prime `p>=2`,

```text
sum_(m>=1) 1/(m p^m)
 <=sum_(m>=1)p^(-m)
 =1/(p-1)
 <=2/p.                                                (EN.3)
```

Consequently

```text
E(S_F)
 <=2 sum_(2<=n<=ceil(exp(B_F))+1) log(n)/n
 <=C(1+B_F)^2.                                         (EN.4)
```

The last step is the elementary integral comparison for `log(x)/x`.  No prime
number theorem is used.  Unlike Proof 414 `(WS.24)`, `(EN.4)` controls the
complete `m>=1` energy; the canonical base cutoff pays for the tail.

This changes the route judgment:

```text
global Euler H^(1/2) budget for arbitrary S:  rejected;
global Euler H^(1/2) budget for S_F:          polynomial. (EN.5)
```

Equation `(EN.4)` does not by itself control off-diagonal boundary terms.
Proof 415 `(CF.15)` still forbids replacing the full response by the diagonal
ledger.

## 6. Exact remaining theorem

Keep Proof 415's completed weighted boundary form

```text
Lambda_(S_F)(F)
 =Tr[
   G_(S_F)^(-1) mathcalB_(h_(S_F))(w_F)
   -G_0^(-1) mathcalB_(h_0)(w_F)].                    (EN.6)
```

The next sufficient theorem is a Burnol-specific energy-to-boundary estimate
of the form

```text
abs Lambda_(S_F)(F)
 <=C_lambda (1+B_F)^d
      P(E(S_F)) norm(F)_(R_(B_F)^r),                  (EN.7)
```

for one fixed polynomial `P`, or the corresponding diagonal root bound along
the resonant Yoshida family.  Inserting `(EN.4)` would make `(EN.7)` polynomial
in support and close the canonical Gate 3U estimate after Proof 336's far
lane.

The theorem must use all of the following source structure:

```text
canonical, deduplicated prime bases;
coefficients p^(-m/2)/m;
the completed outer-minus-Sonin/prolate boundary form;
the fixed Burnol singular-inner carrier;
one relative trace with its anomaly retained.          (EN.8)
```

Near invariance, finite defect, or `(EN.4)` without `(EN.8)` is insufficient.

## 7. Verification

The import-facing WSL2 audit target is

```text
ConnesWeilRH.Dev.CCM24FiniteSCanonicalFamilyAudit.      (VR.1)
```

The focused build passes.  The audited support equivalence, nonzero-term,
visible-prime, and cutoff theorems use exactly

```text
[propext, Classical.choice, Quot.sound].                (VR.2)
```

The companion certificate

```text
docs/proofs/416_canonical_family_energy_and_defect_guard_probe.py
```

builds the literal weighted Toeplitz Gram, checks `(FD.6)`, and compares the
computed response with `2Mr`.  It verifies finite algebra only; the analytic
proof is `(FD.4)--(FD.9)`.

## 8. Decision

```text
Proof 415 exact-support bridge:             closed in Lean;
canonical visible-prime cutoff:            closed in Lean;
arbitrary-S energy divergence guard:       retained;
canonical full Euler energy:               polynomial `(EN.4)`;
finite-defect-only endpoint shortcut:      rejected by `(FD.9)`;
Burnol canonical energy-to-boundary bound: open `(EN.7)`;
Gate 3U / finite-S sign / Burnol / RH:      open / open / open / unproved.
```
