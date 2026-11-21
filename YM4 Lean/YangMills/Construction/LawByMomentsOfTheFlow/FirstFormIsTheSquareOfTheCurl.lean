import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
def maxwellFormAtZeroStatement : Prop :=
  ∀ (a : ℝ) (L m : ℕ) [NeZero m] (A : TorusFields.TorusBond m → ℝ),
    WeightedResponses.maxwellForm a L 0 A A =
      ∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite m)), WeightedResponses.curl A p ^ 2
end YangMills.Construction.MomentLaw
end
