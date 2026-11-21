import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
abbrev UnitLatticeSymmetry : Type := LatticeSymmetry 1
variable {a : ℝ}
def LatticeSymmetry.setImage (r : LatticeSymmetry a) (D : Set AmbientSpace) : Set AmbientSpace :=
  r.toFun '' D
def LatticeSymmetry.comp (r r' : LatticeSymmetry a) : LatticeSymmetry a where
  toFun := r.toFun ∘ r'.toFun
  preservesDist x y := (r.preservesDist _ _).trans (r'.preservesDist x y)
  image_eq := by rw [image_comp, r'.image_eq, r.image_eq]
instance instMulLatticeSymmetry : Mul (LatticeSymmetry a) := ⟨LatticeSymmetry.comp⟩
end YangMills.Construction.InfiniteLattice
