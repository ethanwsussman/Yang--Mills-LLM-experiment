import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields StepCosts RenormalizationStepParameters BlockAverages
namespace LevelShares
def LevelShareBoundedContinuous : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ y : ℝ, T.floorMin ≤ y → ∀ (t n : ℕ) [NeZero n], T.n₀ ≤ n →
    ∀ z : TorusSite n, ∃ C : ℝ,
    ∀ W : TorusField n, IsCold T.threshold W →
      |levelShare T.coupling T.side t Finset.univ z W| ≤ C ∧
        ContinuousAt (fun W' : TorusField n => levelShare T.coupling T.side t Finset.univ z W') W
end LevelShares
end YangMills.Construction
end
