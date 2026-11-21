import YangMills.Construction.InfiniteLattice.HypercubicMotionsOfTheLattice
import YangMills.Construction.InfiniteLattice.ObservablesHypercubicLatticeMapsAndHyperplanes
import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def shiftMotion (v : LatticePoint a) : latticeMotions a :=
  ⟨shiftMap (v : AmbientSpace), LinearMap.id, ⟨1, fun _ => Or.inl rfl⟩, v, v.2, fun _ => rfl⟩
end YangMills.Construction.InfiniteLattice
