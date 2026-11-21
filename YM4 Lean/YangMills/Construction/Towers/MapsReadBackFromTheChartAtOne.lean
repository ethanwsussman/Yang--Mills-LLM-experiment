import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import YangMills.Construction.Towers.PointsAndLogarithmsOfTheChartAtOne
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices (ComplexMatrix2)
open YangMills.Construction.IdentityExpChart
namespace IdentityChartPullback
def Statement : Prop :=
  ∀ L n k j j' : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k → j' ≤ k →
    ∀ [Fintype (PositiveEdge L n k j)] [Fintype (PositiveEdge L n k j')]
      (s : (PositiveEdge L n k j' → ComplexMatrix2.LieElement) → PositiveEdge L n k j → ComplexMatrix2.LieElement),
      (∀ A : Set (PositiveEdge L n k j' → ComplexMatrix2.LieElement), IsOpen A →
        A ⊆ lieBall (PositiveEdge L n k j') (1 / 2) → AnalyticOnNhd ℝ s A →
        MapsTo s A (lieBall (PositiveEdge L n k j) (1 / 2)) →
        IsAnalyticFieldMap (identityChartPoint '' A) fun W => identityChartPoint (s (identityChartLog W))) ∧
      (s 0 = 0 → DifferentiableAt ℝ s 0 → ∀ B ∈ edgeFormSpace L n k j',
        leftDifferential (fun W : Edge L n k j' → ComplexMatrix2 => identityChartPoint (s (identityChartLog W)))
            (trivialField L n k j') B =
          IdentityExpChart.ofValues (fderiv ℝ s 0 (formValues B)))
end IdentityChartPullback
end YangMills.Construction.Tower
end
