import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
def NormalizedMeanNearOne : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ n k j : ℕ, 0 < n → j < k →
    ∀ U ∈ Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ e, Matrices.ComplexMatrix2.operatorNorm (U e - 1) < ρ) →
      ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
        meanRadius U c ≠ 0 ∧ ‖meanRadius U c - 1‖ < 1 / 2 ∧
        Matrices.ComplexMatrix2.operatorNorm (normalizedMean U c - 1) < 1 / 2 ∧
        normalizedMean U c ∈ PeriodicLattice.complexGaugeGroup ∧
        ∃ D : (Tower.Edge L n k j → Matrices.ComplexMatrix2) →ₗ[ℝ] Matrices.ComplexMatrix2,
          ∀ (g : Tower.Edge L n k j → Matrices.ComplexMatrix2)
            (γ : ℝ → Tower.Edge L n k j → Matrices.ComplexMatrix2), γ 0 = U →
            (∀ e, HasDerivAt (fun t => γ t e) (g e) 0) →
              HasDerivAt (fun t => normalizedMean (γ t) c) (D g) 0
end RunningCouplingSlope
end YangMills.Construction
end
