import YangMills.Construction.ColdChainAtEveryLevel.FractionalIntegrationOnTheLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFractionalIntegration
def cubicKernelTraceStatement : Prop :=
  ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 < C ∧ ∀ (D E : Finset Lattice4) (μ f : Lattice4 → ℝ) (A : ℝ) (R : ℕ), 1 ≤ R → 0 ≤ A →
    (∀ x, 0 ≤ μ x) → (∀ y, 0 ≤ f y) → (∀ x ∈ E, ∀ y ∈ D, supNorm (x - y) ≤ R) →
    (∀ (x : Lattice4) (r : ℕ), 1 ≤ r → r ≤ R →
      ∑ b ∈ E.filter (fun b => supNorm (b - x) ≤ r), μ b ≤ A * ((r : ℝ) / R) ^ (4 * θ)) →
    ∑ x ∈ E, μ x * (∑ y ∈ D, cubicKernel (x - y) * f y) ^ 4 ≤ C * A * ∑ y ∈ D, f y ^ 4
end YangMills.Construction.LatticeFractionalIntegration
end
