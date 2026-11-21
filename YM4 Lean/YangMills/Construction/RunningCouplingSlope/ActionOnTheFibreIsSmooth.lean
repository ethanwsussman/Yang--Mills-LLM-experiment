import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
def ChainActionFibreContDiff : Prop :=
  ∀ a : ℝ, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ (N : ℕ) (e : (Fin N → ℝ) →ₗ[ℝ] LevelForms L n k),
      ContDiffAt ℝ 2 (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
        chainAction a (fibreMove (expMove (e p.1) (unitPoint L n k)) (e p.2))) 0
end RunningCouplingSlope
end YangMills.Construction
end
