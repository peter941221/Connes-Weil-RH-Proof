import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

/-!
# Physical point-value bump for the P2 profile owner

The P2 finite-prime observable samples the actual compact-log test at
`log n`.  This leaf supplies the smallest physical interpolation primitive:
an interior point of a log interval can be assigned value one by a genuine
`CompactLogTest`.  It does not assert Mellin interpolation, health, or a
Weil sign.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2PhysicalPointBump

open CCM25Concrete.CompactLogConvolution
open scoped ContDiff

noncomputable section

theorem exists_compactLogTest_supported_Icc_eq_one
    {a b x : Real} (hax : a < x) (hxb : x < b) :
    ∃ g : CompactLogTest,
      Function.support g.test ⊆ Set.Icc a b ∧ g.test x = 1 := by
  obtain ⟨u, htsupp, hcompact, hsmooth, _hrange, hux⟩ :=
    exists_contDiff_tsupport_subset (s := Set.Ioo a b) (x := x) (n := ⊤)
      (Ioo_mem_nhds hax hxb)
  let v : Real → Complex := Complex.ofRealCLM ∘ u
  have hvcompact : HasCompactSupport v := hcompact.comp_left (by simp)
  let hvsmooth := Complex.ofRealCLM.contDiff.comp hsmooth
  let g : CompactLogTest :=
    { test := hvcompact.toSchwartzMap hvsmooth
      compactSupport := by simpa [v] using hvcompact }
  refine ⟨g, ?_, ?_⟩
  · intro y hy
    have hyts : y ∈ tsupport v := subset_tsupport v hy
    have hytsu : y ∈ tsupport u := tsupport_comp_subset (by simp) u hyts
    have hyIoo : y ∈ Set.Ioo a b := htsupp hytsu
    exact ⟨le_of_lt hyIoo.1, le_of_lt hyIoo.2⟩
  · simp [g, v, hux]

end
end C1P2PhysicalPointBump
end Source
end ConnesWeilRH
