import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open YangMills.Construction.Tower
def MeanStepNearCovariantDeriv.Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ n k m : ℕ, 0 < n → m < k →
    ∀ V ∈ fieldsIn L n k m PeriodicLattice.complexGaugeGroup,
      (∀ e, Matrices.ComplexMatrix2.operatorNorm (V e - 1) < ρ) → ∀ c : Edge L n k (m + 1), c.IsPositivelyOriented →
        ∀ B ∈ complexEdgeForms L n k m, ∀ s β : ℝ, 0 ≤ s → 0 ≤ β →
          (∀ e ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k m)),
            Matrices.ComplexMatrix2.operatorNorm (V e - 1) ≤ s) →
          (∀ e ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k m)),
            Matrices.ComplexMatrix2.operatorNorm (B e) ≤ β) →
          Matrices.ComplexMatrix2.operatorNorm
            (meanCovariantStep V B c - covariantSmoothingDeriv V B c) ≤ C * s * β
end RunningCouplingSlope
end YangMills.Construction
end
