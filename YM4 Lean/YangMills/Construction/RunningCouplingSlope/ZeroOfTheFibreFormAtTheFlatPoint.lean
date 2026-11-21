import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def FibreHessianKernelAtUnit : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ η : LevelForms L n k, topDeriv (unitPoint L n k) η = 0 →
      fibreSecondDeriv a (unitPoint L n k) η η = 0 →
      ∃ l ∈ topVanishingGauges L n k, η = gaugeOrbitMap (unitPoint L n k) l
end YangMills.Construction.RunningCouplingSlope
end
