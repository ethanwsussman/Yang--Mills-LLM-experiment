import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity
namespace NormalPlanes
def IsAxisNormal (n : Fin 4 → ℝ) : Prop := ∃ μ, n = PeriodicLattice.coordVec μ
def admissibleNormals : Set (Fin 4 → ℝ) :=
  {n | IsAxisNormal n} ∪
    {n | ∃ μ ν : Fin 4, μ < ν ∧
      (n = PeriodicLattice.coordVec μ + PeriodicLattice.coordVec ν ∨
        n = PeriodicLattice.coordVec μ - PeriodicLattice.coordVec ν)}
def normalOverNormSq (n : Fin 4 → ℝ) : Fin 4 → ℝ := (n ⬝ᵥ n)⁻¹ • n
def heightAlong (n x : Fin 4 → ℝ) : ℝ := n ⬝ᵥ x
end NormalPlanes
end ReflectionPositivity
end YangMills.Construction
