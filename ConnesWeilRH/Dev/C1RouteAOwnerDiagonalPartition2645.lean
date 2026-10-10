import ConnesWeilRH.Dev.ZProbe2628K00
import ConnesWeilRH.Dev.ZProbe2628K01
import ConnesWeilRH.Dev.ZProbe2628K02
import ConnesWeilRH.Dev.ZProbe2628K03
import ConnesWeilRH.Dev.ZProbe2628K04
import ConnesWeilRH.Dev.ZProbe2628K05
import ConnesWeilRH.Dev.ZProbe2628K06
import ConnesWeilRH.Dev.ZProbe2628K07
import ConnesWeilRH.Dev.ZProbe2628K08
import ConnesWeilRH.Dev.ZProbe2628K09
import ConnesWeilRH.Dev.ZProbe2628K10
import ConnesWeilRH.Dev.ZProbe2628K11
import ConnesWeilRH.Dev.ZProbe2628K12
import ConnesWeilRH.Dev.ZProbe2628K13
import ConnesWeilRH.Dev.ZProbe2628K14
import ConnesWeilRH.Dev.ZProbe2628K15
import ConnesWeilRH.Dev.ZProbe2628K16
import ConnesWeilRH.Dev.ZProbe2628K17
import ConnesWeilRH.Dev.ZProbe2628K18
import ConnesWeilRH.Dev.ZProbe2628K19
import ConnesWeilRH.Dev.ZProbe2628K20
import ConnesWeilRH.Dev.ZProbe2628K21
import ConnesWeilRH.Dev.ZProbe2628K22
import ConnesWeilRH.Dev.ZProbe2628K23
import ConnesWeilRH.Dev.ZProbe2628K24
import ConnesWeilRH.Dev.ZProbe2628K25
import ConnesWeilRH.Dev.ZProbe2628K26
import ConnesWeilRH.Dev.ZProbe2628K27
import ConnesWeilRH.Dev.ZProbe2628K28
import ConnesWeilRH.Dev.ZProbe2628K29

/-!
# Owner-moment-matrix diagonal partition (records 2634-2644)

The 30 single-entry membership certificates
`actualOwnerMomentMatrix2351_entry{00..29}_mem2628` assemble here into
one quantified statement: every diagonal entry of the actual owner
moment matrix is contained in the corresponding analytic interval of
the committed 2597 table. This is the interface the diagonal campaign
hands to the partition layer's consumers; the claim is exactly the
conjunction of the 30 certified entries — no off-diagonal or assembly
claim beyond the diagonal containment itself.
-/

namespace ConnesWeilRH.Dev

/-- Partition assembly of records 2634-2644: the full owner-moment-matrix
diagonal is covered by the analytic interval table. -/
theorem actualOwnerMomentMatrix2351_diagonal_mem2645 :
    ∀ d : Fin 30, (analyticMomentInterval2597 d d).Mem
      (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 d d) := by
  intro d
  fin_cases d
  exacts [actualOwnerMomentMatrix2351_entry00_mem2628,
          actualOwnerMomentMatrix2351_entry01_mem2628,
          actualOwnerMomentMatrix2351_entry02_mem2628,
          actualOwnerMomentMatrix2351_entry03_mem2628,
          actualOwnerMomentMatrix2351_entry04_mem2628,
          actualOwnerMomentMatrix2351_entry05_mem2628,
          actualOwnerMomentMatrix2351_entry06_mem2628,
          actualOwnerMomentMatrix2351_entry07_mem2628,
          actualOwnerMomentMatrix2351_entry08_mem2628,
          actualOwnerMomentMatrix2351_entry09_mem2628,
          actualOwnerMomentMatrix2351_entry10_mem2628,
          actualOwnerMomentMatrix2351_entry11_mem2628,
          actualOwnerMomentMatrix2351_entry12_mem2628,
          actualOwnerMomentMatrix2351_entry13_mem2628,
          actualOwnerMomentMatrix2351_entry14_mem2628,
          actualOwnerMomentMatrix2351_entry15_mem2628,
          actualOwnerMomentMatrix2351_entry16_mem2628,
          actualOwnerMomentMatrix2351_entry17_mem2628,
          actualOwnerMomentMatrix2351_entry18_mem2628,
          actualOwnerMomentMatrix2351_entry19_mem2628,
          actualOwnerMomentMatrix2351_entry20_mem2628,
          actualOwnerMomentMatrix2351_entry21_mem2628,
          actualOwnerMomentMatrix2351_entry22_mem2628,
          actualOwnerMomentMatrix2351_entry23_mem2628,
          actualOwnerMomentMatrix2351_entry24_mem2628,
          actualOwnerMomentMatrix2351_entry25_mem2628,
          actualOwnerMomentMatrix2351_entry26_mem2628,
          actualOwnerMomentMatrix2351_entry27_mem2628,
          actualOwnerMomentMatrix2351_entry28_mem2628,
          actualOwnerMomentMatrix2351_entry29_mem2628]

end ConnesWeilRH.Dev
