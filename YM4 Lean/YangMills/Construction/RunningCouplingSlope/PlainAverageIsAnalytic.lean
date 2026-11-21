import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def NormalizedMeanAnalytic : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ n k j : ℕ, 0 < n → j < k →
    ∀ [Fintype (Tower.Edge L n k j)], ∀ U ∈ Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ e, Matrices.ComplexMatrix2.operatorNorm (U e - 1) < ρ) →
      ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
        AnalyticAt ℂ (fun U' : Tower.Edge L n k j → Matrices.ComplexMatrix2 => meanRadius U' c) U ∧
        AnalyticAt ℂ (fun U' : Tower.Edge L n k j → Matrices.ComplexMatrix2 => normalizedMean U' c) U
end YangMills.Construction.RunningCouplingSlope
end
