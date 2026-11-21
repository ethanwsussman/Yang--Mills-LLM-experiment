import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBonds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def PlaquettePropertiesAllMeshes.Statement : Prop :=
  ∀ a : ℝ, 0 < a → PlaquetteProperties a
end YangMills.Construction.InfiniteLattice
