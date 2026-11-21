import YangMills.Construction.FreeEnergiesOfTheFlow.MassOfTheFlow
import YangMills.Construction.ResponseInTheExpansion.TheChainIsALaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open TorusFields TorusLumps ClusterExpansionOfAStep WeightedResponses
private theorem chainFunctional_flowCoupling (ℓ : StepParameters) (β : ℝ) :
    ∀ s : ℕ, chainFunctional ℓ β (flowCoupling ℓ β) s = flowFunctional ℓ β s
  | 0 => rfl
  | s + 1 => by
    have h : flowFunctional ℓ β (s + 1) = kernelImage ℓ (flowCoupling ℓ β s) (flowFunctional ℓ β s) := rfl
    rw [h, ← chainFunctional_flowCoupling ℓ β s]
    rfl
theorem flowFunctionalIntegral_of_chainLaw (hL : ChainIsProbabilityLaw) : flowFunctionalIntegral := by
  intro ℓ hadm β t n _
  obtain ⟨-, h1, h2, h3, h4, -, h5, -, -⟩ := hL ℓ hadm hadm.depth_lt β (flowCoupling ℓ β) t n
  rw [chainFunctional_flowCoupling] at h2 h3 h4 h5
  exact ⟨h2, h3, h4, h5, h1⟩
end YangMills.Construction.FreeEnergies
end
