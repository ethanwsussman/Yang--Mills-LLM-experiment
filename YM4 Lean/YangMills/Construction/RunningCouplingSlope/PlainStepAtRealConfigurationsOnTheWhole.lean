import YangMills.Construction.RunningCouplingSlope.OnePlainStepOnTheWhole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
def MeanStepAtCompactFields : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ δ : ℝ, 0 < δ ∧ ∀ k j : ℕ, j < k →
    ∀ V ∈ nearIdentityFields L k j δ, (∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) →
      (∀ c, nextMeanIterate V c ∈ PeriodicLattice.compactGaugeGroup) ∧
      (∀ c : Tower.FullSpace.Edge L k (j + 1), c.IsPositivelyOriented → (meanRadius V c).im = 0) ∧
      ∀ B ∈ Tower.FullSpace.edgeFormSpace (Tower.meshAt L k j), ∀ c,
        meanCovariantStep V B c ∈ Matrices.ComplexMatrix2.hermitianTraceless
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
