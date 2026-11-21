import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
def HolDifferentialLinear : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ n k j : ℕ, 0 < n → j < k →
    ∀ U ∈ Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ e, Matrices.ComplexMatrix2.operatorNorm (U e - 1) < ρ) →
      (∀ (B : Tower.Edge L n k j → Matrices.ComplexMatrix2) (c : Tower.Edge L n k (j + 1)),
        c.IsPositivelyOriented →
        Tower.holLeftDifferential normalizedMean U B c ∈ Matrices.ComplexMatrix2.traceless) ∧
      ∀ (z : ℂ) (B B' : Tower.Edge L n k j → Matrices.ComplexMatrix2),
        Tower.holLeftDifferential normalizedMean U (z • B + B') =
          z • Tower.holLeftDifferential normalizedMean U B +
            Tower.holLeftDifferential normalizedMean U B'
end RunningCouplingSlope
end YangMills.Construction
end
