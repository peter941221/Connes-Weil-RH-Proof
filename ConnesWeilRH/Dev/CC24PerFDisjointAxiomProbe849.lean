import ConnesWeilRH.Basic
import ConnesWeilRH.Source.ZetaHalfNonvanishing
import ConnesWeilRH.Source.DirichletEta

/-!
# 849 probe: is the concrete per-F row `finiteSetDisjointFromNontrivialZeros
# standard cc20TripleFiniteVanishingSet` axiom-clean, or does it rely on an
# unclosed constant ?

848 pinned that the only genuinely remaining "per-F carrier" row of the
constructive CC20 exit is
    finiteSetDisjointFromNontrivialZeros
      RHDefinitionBridge.standard cc20TripleFiniteVanishingSet
(`tripleVanishingMatchesMellin` is `rfl` from `input.tripleVanishing`, and
`finiteSetIsTriple` is `rfl` on the concrete triple — those two are NOT open).

`Source/ZetaHalfNonvanishing.lean` claims a CLOSED theorem
`cc20_triple_disjoint_from_standard_source_nontrivial_zeros`, built from
`riemannZeta_half_ne_zero`.  That proof goes through the Dirichlet-eta
real/analytic identity and various eta/tau identities.  The whole question is:
does the "closed" chain actually reach Mathlib's `riemannZeta`, or does it stop
at an unproved `axiom`/`sorryAx` at the tail?

This file answers with `#print axioms`, and additionally pins the raw
`riemannZeta (1/2) != 0` statement and the eta factor-multiplied identity.
-/

open ConnesWeilRH.Source

-- the concrete per-F disjointness row
#check SourceFiniteSetDisjointFromNontrivialZeros
#check cc20TripleFiniteVanishingSet
#check cc20_triple_disjoint_from_standard_source_nontrivial_zeros
#print axioms cc20_triple_disjoint_from_standard_source_nontrivial_zeros

-- its only arithmetic core
#check riemannZeta_half_ne_zero
#print axioms riemannZeta_half_ne_zero
-- the eta-to-zeta-half identity (the tail of riemannZeta_half_ne_zero)
#print axioms riemannZeta_half_ne_zero_of_dirichletEtaAnalytic_half_eq_ordered
#print axioms dirichletEtaAnalytic_half_eq_ordered