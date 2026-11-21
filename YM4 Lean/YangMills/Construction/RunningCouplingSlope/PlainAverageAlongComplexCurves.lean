import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open YangMills.Construction.Tower
def ContourMeanComplexDerivative : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ n k j : ℕ, 0 < n → j < k →
    ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < ρ) → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        ∃ D : (Edge L n k j → Matrices.ComplexMatrix2) →ₗ[ℂ] Matrices.ComplexMatrix2,
          ∀ (g : Edge L n k j → Matrices.ComplexMatrix2)
          (γ : ℂ → Edge L n k j → Matrices.ComplexMatrix2), γ 0 = V →
          (∀ b, HasDerivAt (fun t => γ t b) (g b) 0) →
            HasDerivAt (fun t => normalizedMean (γ t) c) (D g) 0
end RunningCouplingSlope
end YangMills.Construction
end
