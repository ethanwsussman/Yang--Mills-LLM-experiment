import YangMills.Construction.EuclideanFunctionals.CorrespondenceOfSystemsAndReconstructions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.OSDataOfRecon
open DefinitionComparison
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S),
    ∃ d : OSData σ.space S, Corresponds σ.recon d
end YangMills.Construction.EuclideanFunctionals.OSDataOfRecon
