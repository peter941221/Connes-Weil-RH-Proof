# Proof 659: polar scaled target size

## Result

Let `q_p=p^(-1/2)`, `s_p=sqrt(q_p)/(1+q_p)`, and let `D_(p,S)` be the actual
adjacent left Julia co-defect. Proofs 658 and 659 give

```text
||P_old - P_new||                       <= 4 q_p,
||P_new - A P_new A^*||                 <= 4 q_p,
||D_(p,S)^* D_(p,S)||                   <= 8 q_p,
||D_(p,S)||                             <= 6 s_p.
```

The polar Julia right factor has norm at most `||detector||`. After the
genuine two-sided Schur cofactor, Lean proves

```text
||s_p^(-1) PolarCompleteTarget_(p,S)||
  <= 48 ||detector||.
```

The full same-domain target has the exact split

```text
CompleteTarget = PolarCompleteTarget + NonpolarCompleteTarget.
```

## Boundary

Only the polar share is bounded. The non-polar cofactor remains a signed
first-jet/ordering mismatch and is not zero. Proof 659 does not prove the
arbitrary-suffix Bone 1A bound.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorPolarScaledTargetSize.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorPolarScaledTargetSizeAudit.lean
```

The focused source and audit passed with `3444` and `3445` jobs. The combined
Proof 650--659 audit passed with `3454` jobs. All audited declarations use
exactly `[propext, Classical.choice, Quot.sound]`.
