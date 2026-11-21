import YangMills.Construction.InfiniteLattice.LadderOfMirrorsOfOneFamily
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace NormalFamilies
open InfiniteLattice
namespace MirrorLadder
variable (L : MirrorLadder)
def slabSet : Set AmbientSpace :=
  {x | L.offset ≤ L.normal ⬝ᵥ x ∧ L.normal ⬝ᵥ x ≤ L.offset + (L.spacing : ℝ)}
theorem slabSet_eq_slab_zero : L.slabSet = L.slab 0 := by
  ext x
  simp [slabSet, slab]
end MirrorLadder
end NormalFamilies
end YangMills.Construction
