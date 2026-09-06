import ConnesWeilRH.Dev.C1P2DefectControl
import ConnesWeilRH.Dev.C1LaneRStrictness

/-!
# P2 narrow reference-window certificate

The explicit narrow root is already known to have a strict negative
archimedean term and prime-free square support.  This leaf converts that
strict sign into the exact negative `ICgate` certificate consumed by the
same-owner P2 witness interfaces.  It supplies no detector comparison or
defect budget.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2NarrowWindowCertificate

open C1LaneRNarrowArch
open C1LaneRStrictness
open C1P2DefectControl
open C1OrbitWindowSemiLocalGate
open C1LocalConfigurationDomination
open C1SameOwnerWeil
open CCM25Concrete.CompactLogConvolution

noncomputable section

theorem narrowArchRoot_ICgate_neg :
    ICgate narrowArchRoot.convolutionSquare < 0 := by
  unfold ICgate
  rw [finitePrimeSum_eq_zero_of_support_subset_open_log_two
    narrowArchRoot.convolutionSquare narrowArchRoot_square_support_subset_open_log_two]
  simpa using narrowArchRoot_archimedeanTerm_neg

theorem narrowArchRoot_exists_gate_certificate :
    ∃ μ : ℝ,
      0 < μ ∧ ICgate narrowArchRoot.convolutionSquare ≤ -μ := by
  refine ⟨-ICgate narrowArchRoot.convolutionSquare, ?_, ?_⟩
  · exact neg_pos.mpr narrowArchRoot_ICgate_neg
  · linarith

theorem narrowArchRoot_gate_certificate_of_margin
    {μ : ℝ}
    (hmargin : μ ≤ -ICgate narrowArchRoot.convolutionSquare) :
    ICgate narrowArchRoot.convolutionSquare ≤ -μ := by
  linarith

/-! ## Fixed-window adapter for the canonical P2 contract -/

/-- The source support of the fixed narrow reference window. -/
theorem narrowArchRoot_support_subset :
    Function.support narrowArchRoot.test ⊆
      Set.Ioo (-(narrowArchRadius / 2)) (narrowArchRadius / 2) := by
  have hbase : Function.support
      (Dev.M2Width.wideTest narrowArchBaseWidth narrowArchBaseWidth_pos).test ⊆
      Set.Icc (-narrowArchBaseWidth) narrowArchBaseWidth := by
    intro x hx
    have hne : Dev.M2Width.wideBump narrowArchBaseWidth x ≠ 0 := by
      intro hzero
      apply hx
      rw [Dev.M2Width.wideTest_apply]
      simp [hzero]
    exact Dev.M2Width.wideBump_mem_Icc narrowArchBaseWidth
      narrowArchBaseWidth_pos x hne
  have hroot := C1LaneRD3Root.tripleVanishingRoot_support_subset_Icc
    (Dev.M2Width.wideTest narrowArchBaseWidth narrowArchBaseWidth_pos) hbase
  intro x hx
  have hx' := hroot hx
  rcases hx' with ⟨hxlow, hxhigh⟩
  dsimp [narrowArchBaseWidth] at hxlow hxhigh
  constructor <;> nlinarith [narrowArchRadius_pos]

/-- A fixed-window canonical producer payload.  The reference window is no
longer a producer field: only detector support, the explicit same-owner
defect budget, and its scalar margin remain to be supplied. -/
structure P2NarrowReferenceCanonicalWitness (g : CompactLogTest) where
  epsilon : ℝ
  b : ℝ
  hgsupp : Function.support g.test ⊆ Set.Ioo (-b) b
  hbudget :
    (|Real.log (4 * Real.pi) + Real.eulerMascheroniConstant| *
        SchwartzMap.seminorm ℂ 0 0
          (ICdefect g.convolutionSquare {()}
            (fun _ => narrowArchRoot.convolutionSquare) (fun _ => 1)).test +
      archimedeanIntegralNorm (ICdefect g.convolutionSquare {()}
        (fun _ => narrowArchRoot.convolutionSquare) (fun _ => 1))) +
    ∑ n ∈ globalPrimeIndexSet (ICdefect g.convolutionSquare {()}
        (fun _ => narrowArchRoot.convolutionSquare) (fun _ => 1)),
      ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ *
        ‖((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ)‖ *
          (2 * (SchwartzMap.seminorm ℂ 0 0 g.convolutionSquare.test +
            SchwartzMap.seminorm ℂ 0 0 narrowArchRoot.convolutionSquare.test)) ≤
    epsilon
  hmargin : epsilon ≤ -ICgate narrowArchRoot.convolutionSquare

/-- The fixed-window payload expands to the existing canonical P2 witness
without changing the detector or introducing a second owner. -/
noncomputable def P2NarrowReferenceCanonicalWitness.toCanonical
    (g : CompactLogTest) (p : P2NarrowReferenceCanonicalWitness g) :
    P2CanonicalOneWindowBudgetWitness g :=
  { W := narrowArchRoot
    mu := -ICgate narrowArchRoot.convolutionSquare
    epsilon := p.epsilon
    b := p.b
    a := narrowArchRadius / 2
    hgsupp := p.hgsupp
    hWsupp := by
      simpa only [neg_div] using narrowArchRoot_support_subset
    hcert := by
      simpa using
        (narrowArchRoot_gate_certificate_of_margin (μ :=
          -ICgate narrowArchRoot.convolutionSquare) le_rfl)
    hbudget := by simpa using p.hbudget
    hmargin := p.hmargin }

/-- The fixed-window payload directly supplies the detector-specific orbit
gate. -/
theorem orbitGate_of_p2NarrowReferenceCanonicalWitness
    (g : CompactLogTest) (p : P2NarrowReferenceCanonicalWitness g) :
    orbitWindowSemiLocalGate g := by
  exact orbitGate_of_p2CanonicalOneWindowBudgetWitness g
    (P2NarrowReferenceCanonicalWitness.toCanonical g p)

end
end C1P2NarrowWindowCertificate
end Source
end ConnesWeilRH
