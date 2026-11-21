import YangMills.Construction.ClusterExpansionOfAStep.TheExpansionReturns
import YangMills.Construction.RunningCouplingSlope.NumberOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusLumps RenormalizationStepParameters StepReturn RunningCouplingSlope
namespace SlopeCoefficient
def CouplingStepNearSlope (ℓ : StepParameters) (b : ℕ → ℝ) (X C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (D : TorusFunctional), X ≤ x → HasExpansion ℓ t x D →
    ∀ x' : ℝ, HasExpansion ℓ (t + 1) x' (kernelImage ℓ x D) → |x - x' - b t| ≤ C * x ^ (-(1 / 4) : ℝ)
def CouplingStepBound : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ (b : ℕ → ℝ) (Ce ys : ℝ), AreStepCoefficients T.coupling T.side b ∧ 0 < Ce ∧ ∀ y : ℝ, T.floorMin ≤ y →
      ExpansionReturnsAt (T.stepParameters y) → CouplingStepNearSlope (T.stepParameters y) b (max y ys) Ce
end SlopeCoefficient
end YangMills.Construction
end
