# Proof 236: unscaled Yoshida selected-owner bridge

Date: 2026-07-14

Status: axiom-clean Lean connection from the support-growing Yoshida factor
to the existing selected convolution-square owner and its whole-line
finite-prime crossing operator. The construction now normalizes the actual
Hermitian square, not only one source factor value. The finite-prime trace
theorem retains explicit interval-basis witnesses. The semilocal positive
owner, integrated same-domain sign, route rewire, and RH remain open.

## 1. The missing Hermitian value

For a compact log test `H`, the selected owner uses

```text
H^star * H.
```

The source convolution and involution laws give

```text
Laplace(H^star * H)(rho)
  =conj(Laplace(H)(-conj(rho))) * Laplace(H)(rho).    (H.1)
```

Consequently

```text
Laplace(H)(rho)=1
```

does not by itself normalize the selected square. The companion value
`Laplace(H)(-conj(rho))` is independent unless additional symmetry has been
proved. Treating one value as sufficient would connect the detector to a
different mathematical object.

The new construction interpolates both points in the Hermitian orbit:

```text
targetNodes={rho,-conj(rho)},
Laplace(H)(rho)=1,
Laplace(H)(-conj(rho))=1.
```

Equation `(H.1)` then proves

```text
Laplace(H^star * H)(rho)=1.                          (H.2)
```

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

## 3. Hermitian square assembly

The theorem
`exists_fixedWindows_nearbyZero_unscaled_hermitian_square_assembly` performs
the same construction with both Hermitian target points. For one final
factor `H` it returns

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
the correction.

## 4. Selected owner and finite-prime operator

`UnscaledYoshidaSelectedOwner.selectedOwner` is definitionally

```text
SelectedWeilSquareOwner.ofCompactLogTest H.
```

Therefore its fields reduce without transport:

```text
owner.sourceTest       =H,
owner.convolutionSquare=H^star * H.                  (H.3)
```

The theorem `exists_fixedWindows_nearbyZero_selectedOwner` combines `(H.2)`
and `(H.3)`. The generated owner detects `rho`, cancels the selected
non-target nodes, and retains the same source support and far-tail bound.

For any finite prime-power family, the same owner then defines

```text
K_S=sum_(p,m) 1/(m sqrt(p^m))
      * (crossing_(p,m)+crossing_(p,m)^dagger).
```

The new wrappers prove

```text
K_S is compact;
K_S is self-adjoint;
ordinaryTrace(K_S)
  =sum_(p,m) owner.finitePrimeTerm(p^m).              (H.4)
```

The compactness and trace statements in `(H.4)` deliberately retain one
`GlobalPrimePowerTraceBasisData` witness per `(p,m)` and a named whole-line
Hilbert basis. These are the existing analytic factorization witnesses. An
axiom audit cannot erase ordinary theorem parameters, so `(H.4)` is not a
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
  line 345   exists_fixedWindows_nearbyZero_unscaled_hermitian_square_assembly

ConnesWeilRH/Source/CCM25Concrete/UnscaledYoshidaSelectedOwner.lean
  line 32    selectedOwner
  line 52    selectedOwner_laplaceAt_convolutionSquare_eq_one
  line 89    operatorSum_isCompactOperator
  line 107   operatorSum_isSelfAdjoint
  line 118   ordinaryTraceAlong_operatorSum_eq_finitePrimeTerm_pow_sum
  line 143   exists_fixedWindows_nearbyZero_selectedOwner
```

The import-facing audit prints both the full theorem types and their axioms.
The selected-owner existence theorem has no premise beyond its displayed
strip, window, and epsilon inputs. The operator trace theorem visibly prints
the basis witnesses described above.

The isolated WSL verification mirror passed these targets:

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

## 6. Route judgment

```text
normalized base constructed inside prescribed window: exact
fixed threshold before nearby-zero radius:             exact
Hermitian companion normalization:                     exact
actual selected square detects rho:                    exact
selected non-target square cancellation:               exact
same-owner finite-prime operator:                       exact
operator self-adjointness:                              unconditional
operator compactness and ordinary trace:                basis witnesses explicit
semilocal positive owner:                               open
integrated sign of -2 Id+K_(S,I):                       open
Lean RH route rewire:                                   none
RH:                                                     unproved
```

The detector and finite-prime ledger now meet on one selected owner. The
remaining hard step is not another ownership bridge: it is the same-domain
sign of the complete semilocal remainder on the common three-Mellin-row
kernel.
