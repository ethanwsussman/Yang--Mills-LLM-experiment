import YangMills.Construction.RunningCouplingSlope.PlainSaddlesOnTheWholeLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
def NormalizedMeanNearIdentity : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ k m : ℕ, m < k →
    ∀ V ∈ Tower.FullSpace.fieldsValuedIn L k m PeriodicLattice.complexGaugeGroup,
      (∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < δ) →
      ∀ c : Tower.FullSpace.Edge L k (m + 1), c.IsPositivelyOriented →
        Matrix.det (contourMean V c) ∈ Complex.slitPlane ∧ meanRadius V c ≠ 0 ∧
        Matrices.ComplexMatrix2.operatorNorm (normalizedMean V c - 1) < ε ∧
        normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup ∧
        ((∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) →
          meanRadius V c = (((meanRadius V c).re : ℝ) : ℂ) ∧ 0 < (meanRadius V c).re ∧
            normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup)
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
