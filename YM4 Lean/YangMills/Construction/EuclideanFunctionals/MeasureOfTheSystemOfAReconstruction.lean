import YangMills.Construction.EuclideanFunctionals.CorrespondenceOfSystemsAndReconstructions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.DefinitionComparison
def ReconSystemMeasuresAgree : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S)
    (s : OSDataOf σ), MeasuresAgree s
end YangMills.Construction.EuclideanFunctionals.DefinitionComparison
