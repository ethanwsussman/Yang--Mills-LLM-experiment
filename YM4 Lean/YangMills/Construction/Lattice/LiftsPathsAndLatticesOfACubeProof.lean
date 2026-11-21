import YangMills.Construction.Lattice.ClosedCubesOfTheCoarseSitesOfACubeProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.CubeCovering
namespace CubeLatticeLift
variable {L m : ℕ}
theorem mem_closedCube_iff {c x : Space} {a : ℝ} :
    x ∈ closedCube c (8 * a) ↔ ∀ μ, c μ - 4 * a ≤ x μ ∧ x μ ≤ c μ + 4 * a := by
  change (∀ μ, |x μ - c μ| ≤ 8 * a / 2) ↔ _
  simp only [abs_le]
  refine forall_congr' fun μ => ?_
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
theorem levelScale_pos (C : CubeData L m) (n : ℕ) : 0 < C.levelScale n := by apply _root_.YangMills.Construction.CubeCovering.CoarseSiteCubes.levelScale_pos <;> assumption
end CubeLatticeLift
end YangMills.Construction.CubeCovering
