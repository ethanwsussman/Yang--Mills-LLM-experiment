import YangMills.Construction.Lattice.CubesOfASeparatedSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CubeCovering
namespace CubeSide
def latticeCube (a : ℝ) (v : Fin 4 → ℤ) : Set Space := closedCube (fun μ => (v μ : ℝ) * a) a
theorem mem_closedCube {c x : Space} {t : ℝ} :
    x ∈ closedCube c t ↔ ∀ μ, |x μ - c μ| ≤ t / 2 := Iff.rfl
end CubeSide
end YangMills.Construction.CubeCovering
