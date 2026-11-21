import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import YangMills.Construction.Towers.PointsAndLogarithmsOfTheChartAtOne
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace Tower
open IdentityExpChart Matrices
def SmoothingOnIdentityLieBallStatement : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∀ [Fintype (PositiveEdge L n k i)] [Fintype (PositiveEdge L n k (i + 1))],
      (∀ ξ ∈ edgeFormSpace L n k i, linearSmoothing L n k i ξ ∈ edgeFormSpace L n k (i + 1)) ∧
      ∃ T ∈ 𝓝 (0 : PositiveEdge L n k i → ComplexMatrix2.LieElement),
        T ⊆ lieBall (PositiveEdge L n k i) (1 / 2) ∧
        MapsTo (fun y => smoothingStep L n k i (identityChartPoint y)) T
          (identityChartPoint '' lieBall (PositiveEdge L n k (i + 1)) (1 / 2)) ∧
        ∀ A : Set (PositiveEdge L n k i → ComplexMatrix2.LieElement), IsOpen A → A ⊆ T →
          IsAnalyticFieldMap (identityChartPoint '' A) (smoothingStep L n k i) ∧
            ∀ V ∈ identityChartPoint '' A, ∀ B' ∈ edgeFormSpace L n k (i + 1),
              ∃ B ∈ edgeFormSpace L n k i, leftDifferential (smoothingStep L n k i) V B = B'
end Tower
end YangMills.Construction
end
