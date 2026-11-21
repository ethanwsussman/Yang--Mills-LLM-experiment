import YangMills.Construction.EuclideanFunctionals.CorrespondenceOfSystemsAndReconstructions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ReconOfOSData
open DefinitionComparison
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (τ : SymmEuclidFunctional m S),
    ∃ R : OSReconstruction τ.space S, Corresponds R τ.osData
end YangMills.Construction.EuclideanFunctionals.ReconOfOSData
