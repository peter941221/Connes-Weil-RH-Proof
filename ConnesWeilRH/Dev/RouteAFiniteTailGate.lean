import Mathlib.Analysis.InnerProductSpace.PiL2
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace

/-!
# Route-A finite-carrier tail Gate closure

Route A re-points the Gate to a *finite* Hilbert--Schmidt carrier (AGENTS
A1/A2 seam blocks transport onto the infinite-dim `sourceSoninCarrier`, see
`docs/proofs/860`).  This module closes the finite tail readout in one step:

```text
trace vs op-norm  :  |Re Tr_along b T| <= (card of b index) * ||T||
                     (PositiveTrace bridge, axiom-free)
tail op-norm RHS  :  ||T|| <= C0 * exp(-B/4) * prod_p quarter-mass
                     (the real constant shape, see TailBound :751)
=> |Re Tr T|      :  <= (card) * C0 * exp(-B/4) * prod          (this file)
```

Honest scope (no over-claim): this proves the *finite* HS-carrier (route-A)
Gate readout only.  It does NOT transport or claim a trace-class certificate
for the original infinite-dimensional `sourceSoninCarrier` renewal tail (a
separate, docs/860-blocked seam).
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete

open scoped ComplexConjugate InnerProduct
open ConnesWeilRH.Source.CC20Concrete.PositiveTrace

namespace RouteAFiniteTailGate

/-- Route-A finite tail Gate, generic form.  If a finite-carrier operator `T`
satisfies the route's tail operator-norm bound `||T|| <= C0 * exp(-B/4) * tau`
(the exact RHS shape of `norm_inverseLowerFactorPhysicalRenewalTailResponse_le_const_exp`,
`CCM24FiniteSCausalMarkovRawRenewalTailBound:751`), then the real-part ordinary
trace readout closes as `|Re Tr| <= (card) * C0 * exp(-B/4) * tau`. -/
theorem finite_tail_gate_of_opNorm_bound
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) [Fintype ι]
    (T : H →L[ℂ] H)
    (C0 B tau : ℝ)
    (hTail : ‖T‖ ≤ C0 * (Real.exp (-B / 4) * tau)) :
    ‖(ordinaryTraceAlong b T).re‖ ≤
      (Fintype.card ι : ℝ) * (C0 * (Real.exp (-B / 4) * tau)) := by
  have htr := abs_re_ordinaryTraceAlong_le_card_mul_opNorm b T
  have hc : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  exact le_trans htr (mul_le_mul_of_nonneg_left hTail hc)

end RouteAFiniteTailGate

end CCM25Concrete
end Source
end ConnesWeilRH

