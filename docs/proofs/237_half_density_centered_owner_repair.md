# Proof 237: half-density centered owner repair

Date: 2026-07-14

Status: axiom-clean Lean repair of Proof 236's source-to-selected coordinate
error.  The support-growing Yoshida factor is now converted by the explicit
half-density multiplier before entering `SelectedWeilSquareOwner`.  The same
owner detects the centered Burnol point, cancels nearby source zeros at their
centered points, and retains a fourth-order square tail.  This proof's
construction gives the positive target value `+1`.  Proof 238 subsequently
replaces that target pattern by a collision-safe negative orbit.  The
semilocal positive owner, integrated remainder sign, route rewire, and RH
remain open.

## 1. Failure mechanism

Let `s` be the source Mellin coordinate and put

```text
u=s-1/2.
```

For a raw compact log test `H`, define the half-density shift

```text
H_c(x)=exp(x/2)H(x).
```

Its bilateral Laplace transform satisfies

```text
Laplace(H_c)(u)=Laplace(H)(u+1/2)=Laplace(H)(s).      (C.1)
```

The selected convolution square uses the centered involution

```text
Laplace(H_c^star*H_c)(u)
  =conj(Laplace(H_c)(-conj(u))) Laplace(H_c)(u).
```

Since

```text
-conj(s-1/2)+1/2=1-conj(s),                          (C.2)
```

equations `(C.1)` and `(C.2)` give the exact source-coordinate identity

```text
Laplace(H_c^star*H_c)(s-1/2)
  =conj(Laplace(H)(1-conj(s))) Laplace(H)(s).         (C.3)
```

Proof 236 instead fed `H` directly to the selected owner and paired `s` with
`-conj(s)`.  Its raw square theorem was true, but it was not equation `(C.3)`.

The coordinate flow is therefore

```text
source test H at {s,1-conj(s)}
                |
                | multiply by exp(x/2)
                v
selected test H_c at {u,-conj(u)}
                |
                v
selected square H_c^star*H_c at u=s-1/2.
```

## 2. Explicit Lean owner

`UnscaledYoshidaSelectedOwner.halfDensityShift` constructs `H_c` as a genuine
`CompactLogTest`.  It proves three ownership facts:

```text
halfDensityShift_apply
laplaceAt_halfDensityShift
halfDensityShift_support_subset
```

The exponential multiplier never vanishes, so the compact support window is
unchanged.  `selectedOwner base correction n` is now definitionally

```text
SelectedWeilSquareOwner.ofCompactLogTest
  (halfDensityShift
    ((convolutionIterate base n).convolution correction)).
```

Thus the half-density conversion is part of the owner, not an external
equality between unrelated witnesses.

The theorem
`selectedOwner_laplaceAt_convolutionSquare_centered` formalizes `(C.3)` for
the exact assembled source factor.  Its two normalization inputs are now

```text
Laplace(H)(rho)=1,
Laplace(H)(1-conj(rho))=1,
```

and `selectedOwner_laplaceAt_convolutionSquare_eq_one` concludes

```text
Laplace(owner.convolutionSquare)(rho-1/2)=1.          (C.4)
```

## 3. Same-witness source-orbit assembly

The new source theorem
`exists_fixedWindows_nearbyZero_unscaled_sourceOrbit_assembly` constructs a
single raw factor normalized on

```text
{rho,1-conj(rho)}.
```

For every selected source node `z` outside that pair, the same factor obeys

```text
Laplace(H)(z)=0.
```

After the half-density shift, the same-owner selected square therefore obeys

```text
Laplace(owner.convolutionSquare)(z-1/2)=0.            (C.5)
```

The quantifier order remains the fixed-threshold order from Proof 235:

```text
construct base and threshold T
        |
        v
choose nearby radius R
        |
        v
choose correction, decay constant C, and power count n.
```

The support is still stated honestly as

```text
((n+1)baseLower+lower, (n+1)baseUpper+upper).
```

## 4. Square tail

The raw assembly supplies the quadratic bound both at `z` and at its source
companion `1-conj(z)`.  The latter remains in the closed source strip because

```text
Re(1-conj(z))=1-Re(z),
Im(1-conj(z))=Im(z).
```

Multiplying the two estimates and using `(C.3)` gives

```text
|z-rho|^2 |(1-conj(z))-rho|^2
  * |Laplace(owner.convolutionSquare)(z-1/2)|
  < epsilon^2.                                      (C.6)
```

`selectedOwner_convolutionSquare_doubleDistance_bound_lt` proves the
algebraic multiplication step.  The final theorem
`exists_fixedWindows_nearbyZero_selectedOwner` returns `(C.4)`, `(C.5)`, and
`(C.6)` for one owner.

## 5. Verification evidence

The production declarations are in:

```text
ConnesWeilRH/Source/CC20YoshidaFullProduct.lean
  line 549  exists_fixedWindows_nearbyZero_unscaled_sourceOrbit_assembly

ConnesWeilRH/Source/CCM25Concrete/UnscaledYoshidaSelectedOwner.lean
  line 33   halfDensityShift
  line 54   laplaceAt_halfDensityShift
  line 64   halfDensityShift_support_subset
  line 134  selectedOwner_laplaceAt_convolutionSquare_centered
  line 328  selectedOwner_convolutionSquare_doubleDistance_bound_lt
  line 441  operatorSum_isCompactOperator
  line 459  operatorSum_isSelfAdjoint
  line 470  ordinaryTraceAlong_operatorSum_eq_finitePrimeTerm_pow_sum
  line 496  exists_fixedWindows_nearbyZero_selectedOwner
```

The isolated WSL verification mirror passed direct Lean checking and these
import-facing targets:

```text
ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner
ConnesWeilRH.Dev.CC20YoshidaFullProductAudit
ConnesWeilRH.Dev.UnscaledYoshidaSelectedOwnerAudit
ConnesWeilRH.Source.CCM25Concrete
```

The owning build completed 3509 jobs.  Every new audited declaration reports
only

```text
propext
Classical.choice
Quot.sound
```

and no `sorryAx` or project axiom.

## 6. Route judgment

```text
raw source target rho:                               exact
raw source companion 1-conj(rho):                    exact
half-density shift inside selected owner:            exact
selected target u=rho-1/2:                           exact
selected square normalization at u:                  exact
nearby-zero cancellation at z-1/2:                   exact
fourth-order selected-square tail:                   exact
same-owner finite-prime crossing wrappers:           preserved
negative off-line orbit contribution -2:             closed by Proof 238
finite-S bad-space orthogonality:                     open
semilocal positive owner and same-domain sign:        open
Lean RH route rewire:                                 none
RH:                                                   unproved
```

The successor detector theorem interpolates the full source orbit with signs

```text
H(rho)=1,
H(1-conj(rho))=-1,
H(conj(rho))=0,
H(1-rho)=0.
```

After centering, its selected-square orbit sum is `-2`; Proof 238 proves this
for the genuine deduplicated orbit and combines it with this proof's tail and
nearby-zero cancellation.  The actual finite-S semilocal sign owner remains
open.
