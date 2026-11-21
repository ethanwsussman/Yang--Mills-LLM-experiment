import YangMills.Construction.Towers.PointsAndLogarithmsOfTheChartAtOne
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Conventions Matrices
namespace Tower
open IdentityExpChart
def IdentityChartCurvesStatement : Prop :=
  ∀ L n k j : ℕ, IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    ∀ [Fintype (PositiveEdge L n k j)],
      (∀ (I : Set ℝ) (γ : ℝ → Edge L n k j → ComplexMatrix2),
        IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ →
        MapsTo γ I (identityChartPoint '' lieBall (PositiveEdge L n k j) (1 / 2)) →
        DifferentiableOn ℝ (fun t => identityChartLog (γ t)) I ∧
          ((∀ e : Edge L n k j, e.IsPositivelyOriented → DifferentiableOn ℝ (deriv fun t => γ t e) I) →
            DifferentiableOn ℝ (deriv fun t => identityChartLog (γ t)) I)) ∧
      (∀ (I : Set ℝ) (y : ℝ → PositiveEdge L n k j → ComplexMatrix2.LieElement),
        IsOpenIntervalAroundZero I → DifferentiableOn ℝ y I →
        MapsTo y I (lieBall (PositiveEdge L n k j) (1 / 2)) →
        IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I (fun t => identityChartPoint (y t)) ∧
          (DifferentiableOn ℝ (deriv y) I → ∀ e : Edge L n k j, e.IsPositivelyOriented →
            DifferentiableOn ℝ (deriv fun t => identityChartPoint (y t) e) I)) ∧
      ∀ y₀ ∈ lieBall (PositiveEdge L n k j) (1 / 2),
        ∃ D : (PositiveEdge L n k j → ComplexMatrix2.LieElement) →ₗ[ℝ] (Edge L n k j → ComplexMatrix2),
          Function.Injective D ∧
            ∀ (I : Set ℝ) (γ : ℝ → Edge L n k j → ComplexMatrix2),
              IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ →
              MapsTo γ I (identityChartPoint '' lieBall (PositiveEdge L n k j) (1 / 2)) →
              identityChartLog (γ 0) = y₀ → curveTangent γ = D (deriv (fun t => identityChartLog (γ t)) 0)
end Tower
end YangMills.Construction
end
