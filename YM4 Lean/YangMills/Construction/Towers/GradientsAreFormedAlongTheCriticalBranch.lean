import YangMills.Construction.Towers.SignsOfTheResponseOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.CriticalBranchGradients
def GradientsExistAlongBranch : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ m : ℕ, 0 < m →
    ∀ B : Tower.edgeFormSpace L m k k,
    (∀ᶠ t in 𝓝 (0 : ℝ), Tower.CriticalBranchResponse.GradientExistsAt
        (Tower.chosenEnergy L m k k) (Tower.CriticalBranchResponse.expLineField L m k B t)) ∧
    ∀ᶠ t in 𝓝 (0 : ℝ),
      Tower.CriticalBranchResponse.GradientExistsAt (Tower.plaquetteAction L m k)
        (Tower.chosenProlongComp L m k k (Tower.CriticalBranchResponse.expLineField L m k B t))
end YangMills.Construction.Tower.CriticalBranchGradients
end
