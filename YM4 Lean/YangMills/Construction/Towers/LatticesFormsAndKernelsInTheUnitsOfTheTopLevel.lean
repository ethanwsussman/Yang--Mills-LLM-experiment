import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.UnitScale
section Bonds
variable {a : ℝ}
def linkTranslate (b : InfiniteLattice.Link a) (z : InfiniteLattice.LatticePoint a) :
    InfiniteLattice.Link a :=
  ⟨b.initial + z, b.terminal + z, by simpa only [add_sub_add_right_eq_sub] using b.isAdjacent⟩
def integerPoint (a : ℝ) (z : Fin 4 → ℤ) : InfiniteLattice.LatticePoint a :=
  FullSpace.toFiner a (⟨fun μ => (z μ : ℝ), z, fun μ => by simp⟩ : InfiniteLattice.LatticePoint 1)
end Bonds
end YangMills.Construction.Tower.UnitScale
end
