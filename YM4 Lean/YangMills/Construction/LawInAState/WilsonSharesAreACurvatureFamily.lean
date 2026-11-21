import YangMills.Construction.ClusterExpansionOfAStep.FormsOfAFamily
import YangMills.Construction.ClusterExpansionOfAStep.SharesAreACurvatureFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ShareFamilies
open TorusLumps
def WilsonSharesFormCurvatureFamily : Prop :=
  ∀ ℓ : StepParameters, ℓ.Admissible → ∃ C : ℝ, 0 ≤ C ∧ IsCurvatureFamily ℓ C (levelShareFamily ℓ.coupling ℓ.side 0) ∧
    HasCurvatureForm (levelShareFamily ℓ.coupling ℓ.side 0) 1
end YangMills.Construction.ShareFamilies
end
