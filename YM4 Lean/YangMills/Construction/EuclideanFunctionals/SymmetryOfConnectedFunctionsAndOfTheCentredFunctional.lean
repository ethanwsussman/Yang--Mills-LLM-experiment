import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctionalWithReconstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ConnectedSymmetry
def Main : Prop :=
  ∀ S : ConnFamily, ConnectedSymmetric S ↔ IsSymmMultilinReal S
end YangMills.Construction.EuclideanFunctionals.ConnectedSymmetry
