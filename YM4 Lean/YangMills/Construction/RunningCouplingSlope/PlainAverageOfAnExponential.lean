import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
def NormalizedMeanOfExp : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ n k j : ℕ, 0 < n → j < k →
    ∀ A ∈ Tower.complexEdgeForms L n k j, ∀ a : ℝ, 0 ≤ a → a ≤ ρ →
      (∀ e, Matrices.ComplexMatrix2.operatorNorm (A e) ≤ a) →
      ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
        ‖meanRadius (PeriodicLattice.expTwist A fun _ => 1) c - 1‖ ≤ C * a ^ 2 ∧
        ∃ N ∈ Matrices.ComplexMatrix2.traceless, Matrices.ComplexMatrix2.operatorNorm N ≤ C * a ^ 2 ∧
          normalizedMean (PeriodicLattice.expTwist A fun _ => 1) c =
            Matrices.ComplexMatrix2.matExp (Complex.I • (Tower.linearSmoothing L n k j A c + N))
end RunningCouplingSlope
end YangMills.Construction
end
