import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBonds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def LatticeSymmetryPropertiesAtEverySpacing : Prop :=
  ∀ a : ℝ, 0 < a → LatticeSymmetryProperties a
end YangMills.Construction.InfiniteLattice
