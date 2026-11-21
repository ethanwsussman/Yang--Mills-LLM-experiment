import YangMills.Construction.EuclideanFunctionals.CorrespondenceOfSystemsAndReconstructions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.SystemConeCondition
open DefinitionComparison
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S)
    (s : OSDataOf σ), ConeConditionsAgree s
end YangMills.Construction.EuclideanFunctionals.SystemConeCondition
