import YangMills.Construction.ColdChainAtEveryLevel.FractionalIntegrationOnTheLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeFractionalIntegration
def clippedRadius (N : ℕ) (p x : Lattice4) : ℕ := min N (max 1 (supNorm (x - p)))
def radialPowerWeight (N : ℕ) (p : Lattice4) (θ : ℝ) (x : Lattice4) : ℝ :=
  ((clippedRadius N p x : ℝ) / N) ^ (-θ)
def truncatedCubicKernel (R N : ℕ) (v : Lattice4) : ℝ := if supNorm v ≤ R * N then cubicKernel v else 0
def powerWeightKernelStatement : Prop :=
  ∀ R : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (p : Lattice4) (θ : ℝ) (D E : Finset Lattice4) (f : Lattice4 → ℝ),
    1 ≤ N → |θ| ≤ 1 / 8 → (∀ y, 0 ≤ f y) →
      ∑ x ∈ E, (radialPowerWeight N p θ x * ∑ y ∈ D, truncatedCubicKernel R N (x - y) * f y) ^ 4 ≤
        C * (∑ y ∈ D, (radialPowerWeight N p θ y * f y) ^ 2) ^ 2 ∧
      ∑ x ∈ E, (radialPowerWeight N p θ x / (clippedRadius N p x : ℝ) *
          ∑ y ∈ D, truncatedCubicKernel R N (x - y) * f y) ^ 2 ≤
        C * ∑ y ∈ D, (radialPowerWeight N p θ y * f y) ^ 2
end LatticeFractionalIntegration
end YangMills.Construction
end
