import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CutoffLinks
open YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def plaquetteOf (x : LatticePoint a) (μ ν : Fin 4) (h : μ < ν) : ElementaryPlaquette a :=
  ⟨x, μ, ν, h⟩
def ContainsLink (p : ElementaryPlaquette a) (e : Link a) : Prop := e ∈ p.edges
end YangMills.Construction.CutoffLinks
