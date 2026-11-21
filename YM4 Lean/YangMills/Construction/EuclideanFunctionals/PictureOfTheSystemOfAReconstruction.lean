import YangMills.Construction.EuclideanFunctionals.CorrespondenceOfSystemsAndReconstructions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.DefinitionComparison
def ReconSystemPicturesAgree : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S)
    (s : OSDataOf σ), PicturesAgree s
end YangMills.Construction.EuclideanFunctionals.DefinitionComparison
