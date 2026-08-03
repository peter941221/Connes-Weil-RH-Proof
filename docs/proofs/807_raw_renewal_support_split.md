# Proof 807: Raw renewal support split

Date: 2026-08-04

Status: axiom-clean operator-level support split. The physical renewal tail
and the support-polynomial Gate 3U estimate remain open.

## Result

For a finite prime-power family `T`, let `R_T` denote Proof 805's complete
inverse-lower-factor physical renewal response. Each raw atom has the exact
form

```text
raw coefficient(forward, renewal) * physical two-translation kernel,
```

where the kernel retains the order

```text
forward translation
    -> transported Sonin projection
    -> renewal translation.
```

For every displacement cutoff `B`, Lean splits each raw atom and then the
complete response as

```text
R_T = R_T^(displacement <= B) + R_T^(displacement > B).
```

This is an equality of bounded operators on the source Sonin carrier, before
an ordinary trace, real part, or absolute value. Both pieces retain the
fixed-family operator-norm summability of the raw renewal expansion.

The raw scalar coefficient is also identified exactly with the existing
two-sided raw weight after pairing the forward and renewal indices.

## Why It Matters

The compact-root detector can only be used after the physical owner is kept
whole. The split records exactly where a future support-first argument must
act:

```text
paired displacement cutoff
          |
          v
complete physical raw atom
          |
          v
support part + physical tail
          |
          v
future trace-level tail theorem
```

The transported Sonin projection remains between the two translations. It is
therefore invalid to merge them into one displacement translation and infer
physical trace support from coefficient support alone.

## Boundary

Proof 807 does not prove that the tail vanishes, is trace class after an
arbitrary termwise rearrangement, or has a support-polynomial bound. It does
not exchange the raw atom expansion with an ordinary trace.

Consequently Proof 807 does not prove Gate 3U, the finite-S sign, Burnol's
identity, or `_root_.RiemannHypothesis`.

## Lean Owner

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovRawRenewalSupportSplit.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovRawRenewalSupportSplitAudit.lean
```

Key declarations:

```text
finiteEulerPhysicalResponseAtom_eq_signedCoefficient_smul_unweighted
finiteEulerPhysicalRawRenewalAtom_eq_rawCoefficient_smul_unweighted
inverseLowerFactorPhysicalRenewalResponse_eq_sum_rawAtoms
inverseLowerFactorPhysicalRenewalResponse_eq_support_add_tail
abs_rawPhysicalRenewalCoefficient_eq_twoSidedRawWeight
```
