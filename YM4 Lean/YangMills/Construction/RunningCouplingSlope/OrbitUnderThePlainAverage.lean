import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower
def ContourMeanGaugeOrbit : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ n k j : ℕ, 0 < n → j < k →
    ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < ρ) →
      ∀ l : Vertex L n k j → Matrices.ComplexMatrix2, (∀ x, Matrices.ComplexMatrix2.fullTrace (l x) = 0) →
        ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
          leftDifferential normalizedMean V (covDiff V l) c =
            covDiff (normalizedMean V) (restrictVertexFunction (j + 1) l) c
end YangMills.Construction.RunningCouplingSlope
end
