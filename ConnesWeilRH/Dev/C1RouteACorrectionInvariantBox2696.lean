import Mathlib.Topology.MetricSpace.Contracting

namespace ConnesWeilRH.Dev

open Function

/-- A fixed point of a contraction belongs to every complete forward-invariant
set containing a starting point. This lets a certified coefficient box contain
the fixed point of an affine interval map. -/
theorem fixedPoint_mem_of_complete_invariant_set2696
    {T : Type*} [MetricSpace T] [CompleteSpace T]
    {K : NNReal} {f : T -> T} {s : Set T}
    (hf : ContractingWith K f)
    (hcomplete : IsComplete s)
    (hinvariant : Set.MapsTo f s s)
    {x y : T}
    (hx : s x)
    (hfinite : Ne (edist x (f x)) ⊤)
    (hy : IsFixedPt f y) :
    s y := by
  have hexists :=
    hf.exists_fixedPoint' hcomplete hinvariant (hf.restrict hinvariant) hx hfinite
  let z := Classical.choose hexists
  have hspec := Classical.choose_spec hexists
  have hz : s z := hspec.1
  have hzfixed : IsFixedPt f z := hspec.2.1
  have hzy : z = y := hf.fixedPoint_unique' hzfixed hy
  simpa [hzy] using hz

end ConnesWeilRH.Dev
