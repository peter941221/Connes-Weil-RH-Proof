import ConnesWeilRH.Dev.C1CenterTwoCriterionBridge
import ConnesWeilRH.Source.CC20RHExit
import ConnesWeilRH.Source.ZetaHalfNonvanishing

/-!
# C1CenterTwoRHExit - the healthy-owner RH exit ledger statement

The center-`2` chain is now unconditional up to the sign: Gate 2 identifies
the same-owner Weil functional `psi` with the independently defined zero
spectral value, and the criterion bridge reduces the healthy finite-vanishing
criterion to nonnegativity of that spectral value on every vanishing
convolution square.

This module composes that reduction with the generic Yoshida detector
theorem `cc20_proposition_c1_from_yoshida_detector`, instantiating the
finite-set side conditions at the already closed triple rows
(`cc20_triple_finite_set_admissibility`,
`cc20_triple_disjoint_from_standard_source_nontrivial_zeros`).

The resulting capstone states the complete distance to `SourceRH` on the
healthy compact-log owner as exactly two explicit premises:

```text
[premise 1] CC20YoshidaDetectorExists on healthyCC20TestSpace
            (constructive detector transport, still open)
[premise 2] 0 <= spectralWeilValue g.convolutionSquare for every
            vanishing square g (the RH-level sign content)
                        |
                        v
        healthy_spectral_nonneg_sourceRH_of_yoshida_detector
                        |
                        v
                    SourceRH
```

Neither premise is produced here. Discharging premise `2` is RH-equivalent;
it must never be replaced by a carrier datum swap. RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CenterTwoRHExit

open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1CenterTwoCriterionBridge

/-- The healthy finite-vanishing criterion plus a Yoshida detector on the
same owner yields `SourceRH`.  The finite-set side conditions are discharged
by the closed triple rows. -/
theorem healthy_criterion_sourceRH_of_yoshida_detector
    (hdetector :
      CC20YoshidaDetectorExists C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet)
    (hcriterion : C1.healthyCriterionState cc20TripleFiniteVanishingSet) :
    RHDefinitionBridge.standard.SourceRH :=
  cc20_proposition_c1_from_yoshida_detector
    C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet
    cc20_triple_finite_set_admissibility
    cc20_triple_disjoint_from_standard_source_nontrivial_zeros
    hdetector hcriterion

/-- Capstone: with the closed center-`2` Gate 2 readback, the distance to
`SourceRH` on the healthy compact-log owner is exactly the Yoshida detector
transport plus nonnegativity of the independently defined spectral value on
every vanishing convolution square. -/
theorem healthy_spectral_nonneg_sourceRH_of_yoshida_detector
    (hdetector :
      CC20YoshidaDetectorExists C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet)
    (hspectral :
      ∀ g : CompactLogTest,
        CC20VanishesOn C1.healthyCC20TestSpace
          cc20TripleFiniteVanishingSet g →
          0 ≤ C1SpectralWeil.spectralWeilValue g.convolutionSquare) :
    RHDefinitionBridge.standard.SourceRH :=
  healthy_criterion_sourceRH_of_yoshida_detector hdetector
    ((healthyCriterionState_iff_all_vanishing_spectral_nonnegative
        cc20TripleFiniteVanishingSet).mpr hspectral)

end C1CenterTwoRHExit
end Source
end ConnesWeilRH
