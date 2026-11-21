import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctionalWithReconstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.InvarianceComparison
def Holds : Prop :=
  ∀ S : ConnFamily, ConnectedInvariant S ↔ IsLatticeInvariant S
end YangMills.Construction.EuclideanFunctionals.InvarianceComparison
