import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
def CouplingUniqueness.ColdExpansionCouplingUnique : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∀ y : ℝ, T.floorMin ≤ y →
    ∀ (t : ℕ) (x' x'' : ℝ) (D : TorusLumps.TorusFunctional) (g' g'' : TorusLumps.LocalDensity),
      TorusLumps.ColdExpansion (T.stepParameters y) (t + 1) x' D g' →
        TorusLumps.ColdExpansion (T.stepParameters y) (t + 1) x'' D g'' → x' = x''
end YangMills.Construction
end
