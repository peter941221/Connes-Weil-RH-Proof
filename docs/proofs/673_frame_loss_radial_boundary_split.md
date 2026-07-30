# Proof 673: signed radial boundary split of the frame-loss commutator

## Result

The result is good as an exact signed decomposition. It does not estimate the
remaining producer. Proof 672 reduced the relative commutator to the upper
radial carrier; Proof 673 now separates its interior and boundary channels.

For

```text
E   = radialSupportProjection unitSoninScale,
F   = I - E,
P_S = newSuffixRangeProjection unitSoninScale S,
U_p = (cc20GlobalLogTranslation (log p)).toContinuousLinearMap,
```

the source defines

```text
U_p^rad = E U_p E,
C_(p,S)^int = [U_p^rad, P_S],
C_(p,S)^bdry = F U_p P_S.
```

and proves the exact identity

```text
[U_p, P_S] = C_(p,S)^int + C_(p,S)^bdry.
```

The proof uses only the actual projection identities `EP_S=P_S=P_SE` and
the triangularity `P_S U_p F=0` from Proof 672. It keeps both channels signed;
there is no triangle inequality and no cancellation claim.

## Why this is a useful split

The second term has the literal radial-boundary orientation

```text
(I-E) U_p P_S,
```

while the first term stays on the compressed upper carrier. This prevents an
ordinary ambient commutator estimate from silently mixing a finite-boundary
channel with the interior antiresonant graph problem.

The identity does not yet prove that `C_(p,S)^bdry` has a uniform norm bound
for arbitrary `P_S` inputs. The existing radial split proves such support and
norm facts for the actual new-frame column; transferring them to the full
Sonin projection input is a separate source theorem.

## Remaining producer

The active contract remains

```text
||[U_p,P_S](E u)||
  <= L * ||E (I + U_p) (E u)||,
```

uniformly over route-valid `(p,S)`. Proof 673 rewrites its left side as the
sum of the two named channels above, but does not bound either channel or
discard their signed interaction. Gate 3U, the finite-S sign, Burnol's
identity, and RH remain open.

## Lean artifacts

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundarySplit.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundarySplitAudit.lean
```

The source is imported by `ConnesWeilRH/Source/CCM25Concrete.lean`.
