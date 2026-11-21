import YangMills.Construction.InfiniteLattice.ObservablesHypercubicLatticeMapsAndHyperplanes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def LatticeSymmetry.imageSet (r : LatticeSymmetry a) (S : Set AmbientSpace) : Set AmbientSpace :=
  r.toFun '' S
def ElementaryPlaquette.LiesInPlane (p : ElementaryPlaquette a) (μ κ : Fin 4) : Prop :=
  (p.lowAxis = μ ∧ p.highAxis = κ) ∨ (p.lowAxis = κ ∧ p.highAxis = μ)
def IsLatticeMirror (a : ℝ) (H : Set AmbientSpace) : Prop := H ∈ mirrorPlanes a
end InfiniteLattice
end YangMills.Construction
