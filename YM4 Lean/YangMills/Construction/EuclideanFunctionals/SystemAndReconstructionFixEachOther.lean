import YangMills.Construction.EuclideanFunctionals.CorrespondenceOfSystemsAndReconstructions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.MutualDetermination
open DefinitionComparison (PassagesInverse)
def Holds : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : ConnFamily),
    PassagesInverse H S
end YangMills.Construction.EuclideanFunctionals.MutualDetermination
