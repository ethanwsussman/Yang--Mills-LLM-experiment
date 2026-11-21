import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBonds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def SpecificationPropertiesAtEveryMesh : Prop :=
  ∀ (a β : ℝ) (ha : 0 < a), 0 < β → SpecificationProperties ha β
end YangMills.Construction.InfiniteLattice
