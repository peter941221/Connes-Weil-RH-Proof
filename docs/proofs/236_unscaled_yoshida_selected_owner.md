# Proof 236: unscaled Yoshida uncentered square assembly

Date: 2026-07-14

Status: the uncentered convolution-square construction is algebraically valid
and axiom-clean, but its original interpretation as a Burnol-coordinate
selected owner was wrong.  Burnol's selected variable is `u=s-1/2`, while
this construction evaluates the raw source transform at `s`.  Proof 237 adds
the mandatory half-density shift and is the accepted selected-owner bridge.

## 1. The valid uncentered identity

For a compact log test `H`, the raw additive convolution square is

```text
H^star * H.
```

The source convolution and involution laws give

```text
Laplace(H^star * H)(rho)
  =conj(Laplace(H)(-conj(rho))) * Laplace(H)(rho).    (H.1)
```

Consequently, at this same uncentered variable,

```text
Laplace(H)(rho)=1
```

does not by itself normalize the selected square. The companion value
`Laplace(H)(-conj(rho))` is independent unless additional symmetry has been
proved. Treating one value as sufficient would connect the detector to a
different mathematical object.

The construction interpolates both points in this raw Hermitian orbit:

```text
targetNodes={rho,-conj(rho)},
Laplace(H)(rho)=1,
Laplace(H)(-conj(rho))=1.
```

Equation `(H.1)` then proves the algebraically valid statement

```text
Laplace(H^star * H)(rho)=1.                          (H.2)
```

This is not yet Burnol's spectral square.  If `s` is the source Mellin
coordinate, Burnol's coordinate and the required half-density test are

```text
u=s-1/2,
H_c(x)=exp(x/2)H(x).
```

Then

```text
Laplace(H_c)(u)=Laplace(H)(u+1/2),
-conj(u)+1/2=1-conj(s).                              (H.3)
```

Thus the source companion for a selected target `u=s-1/2` is
`1-conj(s)`, not `-conj(s)`.  The original bridge crossed these two
coordinates without applying `(H.3)`.

## 2. Constructed normalized base

Proof 235 still accepted a base already normalized at `rho`. The new theorem
`exists_fixedWindows_nearbyZero_unscaled_normalized_assembly` constructs that
base inside any prescribed log window. It applies the existing finite-node
interpolation with quadratic strip decay, derives one fixed contraction
threshold, and only then chooses the nearby-zero correction and convolution
count.

The dependency order is

```text
prescribed base window
        |
        v
construct base and quadratic bound
        |
        v
fixed contraction threshold T
        |
        v
nearby-zero radius R
        |
        v
correction, decay constant C, power count n.
```

No caller-supplied normalized-base premise remains. The support of the final
source factor is still recorded honestly as

```text
((n+1)baseLower+lower, (n+1)baseUpper+upper).
```

## 3. Scope of the raw square assembly

The theorem
`exists_fixedWindows_nearbyZero_unscaled_hermitian_square_assembly` performs
the same construction with both raw Hermitian target points. For one final
factor `H` it validly returns

```text
Laplace(H)(rho)=1;
Laplace(H)(-conj(rho))=1;
Laplace(H^star * H)(rho)=1;
Laplace(H^star * H)(z)=0
  for every selected z outside {rho,-conj(rho)};
the fixed-threshold far-tail estimate for H;
the explicit growing support of H.
```

All statements refer to the same expression

```text
(convolutionIterate base n).convolution correction.
```

The square-zero claim uses the source factor at `z`: if `Laplace(H)(z)=0`,
then the second factor in `(H.1)` is zero. It does not assume a symmetry of
the correction.  None of these facts identifies `rho` with the centered
Burnol point.

## 4. Withdrawn selected-owner interpretation

The Proof 236 version of `UnscaledYoshidaSelectedOwner.selectedOwner` was
definitionally

```text
SelectedWeilSquareOwner.ofCompactLogTest H.
```

Therefore its fields reduced without transport:

```text
owner.sourceTest       =H,
owner.convolutionSquare=H^star * H.                  (H.4)
```

Those definitional equalities did not repair the coordinate mismatch.  The
former theorem `exists_fixedWindows_nearbyZero_selectedOwner` combined
`(H.2)` with `(H.4)` and therefore detected the raw point `s=rho`; it did not
prove detection at Burnol's point `u=rho-1/2`.  That interpretation is
withdrawn.

Proof 237 changes `selectedOwner` itself to own `H_c`, constructs the source
pair `{rho,1-conj(rho)}`, and states every selected evaluation at the centered
point `rho-1/2`.

For any finite prime-power family, the same owner then defines

```text
K_S=sum_(p,m) 1/(m sqrt(p^m))
      * (crossing_(p,m)+crossing_(p,m)^dagger).
```

The generic finite-prime wrappers prove

```text
K_S is compact;
K_S is self-adjoint;
ordinaryTrace(K_S)
  =sum_(p,m) owner.finitePrimeTerm(p^m).              (H.5)
```

The compactness and trace statements in `(H.5)` deliberately retain one
`GlobalPrimePowerTraceBasisData` witness per `(p,m)` and a named whole-line
Hilbert basis. These are the existing analytic factorization witnesses. An
axiom audit cannot erase ordinary theorem parameters, so `(H.5)` is not a
no-premise theorem. Self-adjointness alone needs neither witness and is
unconditional for every finite family.

## 5. Lean evidence

```text
ConnesWeilRH/Source/CC20YoshidaConvolution.lean
  line 182   exists_laplaceAt_vertical_half_contraction_of_quadratic_bound
  line 1009  exists_nearbyZero_unscaled_indicator_assembly_of_fixedThreshold
  line 1094  exists_nearbyZero_unscaled_normalized_assembly_of_fixedThreshold
  line 1212  exists_fixedWindows_nearbyZero_unscaled_normalized_assembly

ConnesWeilRH/Source/CC20YoshidaFullProduct.lean
  line 452   exists_fixedWindows_nearbyZero_unscaled_hermitian_square_assembly

ConnesWeilRH/Source/CCM25Concrete/UnscaledYoshidaSelectedOwner.lean
  Proof 237 replaces the raw selectedOwner and its existence theorem
```

The import-facing audit established that the raw assembly theorem itself is
axiom-clean.  It could not establish the missing coordinate equation because
that equation was absent from the theorem statement.

The isolated WSL verification mirror passed these targets for the algebraic
construction:

```text
ConnesWeilRH.Dev.UnifiedRemainingGapsYoshidaConvolutionAudit
ConnesWeilRH.Dev.CC20YoshidaFullProductAudit
ConnesWeilRH.Source.CCM25Concrete
ConnesWeilRH.Dev.UnscaledYoshidaSelectedOwnerAudit
```

The combined owning build completed 3509 jobs. Every new audited theorem
reported only

```text
propext
Classical.choice
Quot.sound
```

No new theorem reports `sorryAx` or a project axiom.

## 6. Corrected route judgment

```text
normalized base constructed inside prescribed window: exact
fixed threshold before nearby-zero radius:             exact
raw companion -conj(rho) normalization:                exact
raw uncentered square at rho:                           exact
Burnol coordinate u=rho-1/2:                           absent in Proof 236
source companion 1-conj(rho):                          absent in Proof 236
original selected-owner interpretation:                withdrawn
accepted repair:                                       Proof 237
semilocal positive owner:                               open
integrated sign of -2 Id+K_(S,I):                       open
Lean RH route rewire:                                   none
RH:                                                     unproved
```

The lesson is an ownership guard: a true transform identity at the wrong
coordinate is not a bridge.  The accepted owner must carry the half-density
map as an explicit definition so that the source and selected evaluations can
be checked in the theorem type.
