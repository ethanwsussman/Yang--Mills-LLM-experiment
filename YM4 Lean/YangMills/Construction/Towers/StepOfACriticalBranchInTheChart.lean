import YangMills.Construction.Calculus.AnalyticConstrainedMinimizers
import YangMills.Construction.Towers.ChartAtTheTrivialConfigurationDefs
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace Tower
open IdentityExpChart
abbrev smoothingInExpChart (L n k i : ℕ) :
    (PositiveEdge L n k i → Matrices.ComplexMatrix2.LieElement) →
      PositiveEdge L n k (i + 1) → Matrices.ComplexMatrix2.LieElement :=
  mapOnValues (logPullback (smoothingStep L n k i))
abbrev fnInExpChart {L n k i : ℕ} (F : (Edge L n k i → Matrices.ComplexMatrix2) → ℝ) :
    (PositiveEdge L n k i → Matrices.ComplexMatrix2.LieElement) → ℝ :=
  fnOnValues (funPullback F)
def CriticalStepInExpChart : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∀ [Fintype (PositiveEdge L n k i)] [Fintype (PositiveEdge L n k (i + 1))]
      (F : (Edge L n k i → Matrices.ComplexMatrix2) → ℝ),
      (∃ U : Set (Edge L n k i → Matrices.ComplexMatrix2), IsOpenNhdOfOne U ∧
        IsAnalyticFieldFunction U F) →
      leftGradient (fieldSpace L n k i) (fun V => (F V : ℂ)) (trivialField L n k i) = 0 →
      (∀ ξ ∈ edgeFormSpace L n k i, linearSmoothing L n k i ξ = 0 → ξ ≠ 0 →
        0 < leftSecondDeriv F (trivialField L n k i) ξ ξ) →
      ConstrainedMinima.IsNondegConstrainedCritical (smoothingInExpChart L n k i)
          (fnInExpChart F) ∧
        (∀ y, fderiv ℝ (smoothingInExpChart L n k i) 0 y =
          formValues (linearSmoothing L n k i (ofValues y))) ∧
        ∀ y y', fderiv ℝ (fderiv ℝ (fnInExpChart F)) 0 y y' =
          leftSecondDeriv F (trivialField L n k i) (ofValues y) (ofValues y')
end Tower
end YangMills.Construction
end
