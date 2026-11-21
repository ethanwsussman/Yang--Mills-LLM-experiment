import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def NormalizedMeanOfCompactField : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ n k j : ℕ, 0 < n → j < k →
    ∀ U ∈ Tower.fieldSpace L n k j, (∀ e, Matrices.ComplexMatrix2.operatorNorm (U e - 1) < ρ) →
      ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
        meanRadius U c = (((meanRadius U c).re : ℝ) : ℂ) ∧ 0 < (meanRadius U c).re ∧
          normalizedMean U c ∈ PeriodicLattice.compactGaugeGroup
end YangMills.Construction.RunningCouplingSlope
end
