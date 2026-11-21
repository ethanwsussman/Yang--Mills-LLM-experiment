import YangMills.Construction.EuclideanFunctionals.CorrespondenceOfSystemsAndReconstructions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.DefinitionComparison
def TwoDefinitionsAgree : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily),
    PropertiesAgree m S ∧
    (∀ σ : EuclidFunctionalWithRecon m S, Nonempty (OSDataOf σ)) ∧
    (∀ τ : SymmEuclidFunctional m S, Nonempty (ReconOf τ)) ∧
    (∀ (ℋ : Type) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ],
      PassagesInverse ℋ S) ∧
    (Nonempty (SymmEuclidFunctional m S) ↔
      Nonempty (EuclidFunctionalWithRecon m S)) ∧
    ∀ (σ : EuclidFunctionalWithRecon m S) (s : OSDataOf σ),
      ObjectsAgree s
end YangMills.Construction.EuclideanFunctionals.DefinitionComparison
