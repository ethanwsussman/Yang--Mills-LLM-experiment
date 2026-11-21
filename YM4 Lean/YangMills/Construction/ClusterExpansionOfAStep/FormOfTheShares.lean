import YangMills.Construction.ClusterExpansionOfAStep.FormsOfAFamily
import YangMills.Construction.ClusterExpansionOfAStep.SharesAreACurvatureFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ShareFamilies
def LevelSharesHaveUnitCurvatureForm : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∀ t : ℕ,
    TorusLumps.HasCurvatureForm (levelShareFamily T.coupling T.side (t + 1)) 1
end YangMills.Construction.ShareFamilies
end
