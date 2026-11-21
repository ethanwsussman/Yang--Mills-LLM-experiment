import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
def ResponseContractsCurvatureStatement : Prop :=
  HoldsOnParameterFamilies fun Tb _ => ∀ (u n : ℕ) [NeZero n], 64 ≤ n →
    ∀ (A : TorusFields.TorusBond n → ℝ) (s : ℝ),
    (∀ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite n)), |WeightedResponses.curl A p| ≤ s) →
    ∀ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite (n * Tb.side))),
      |WeightedResponses.curl (WeightedResponses.responseMap Tb.coupling Tb.ρA Tb.side u A) p| ≤ s / 8
end YangMills.Construction.ResponseInTheExpansion
end
