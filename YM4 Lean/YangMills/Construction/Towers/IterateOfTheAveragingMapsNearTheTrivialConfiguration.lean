import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def SmoothingIterAnalyticNearOne : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∃ U : Set (Edge L n k 0 → Matrices.ComplexMatrix2), IsOpenNhdOfOne U ∧
      IsAnalyticFieldMap U (smoothingIter L n k (i + 1)) ∧
      ∀ B ∈ edgeFormSpace L n k 0,
        leftDifferential (smoothingIter L n k (i + 1)) (trivialField L n k 0) B =
          linearSmoothingIter L n k (i + 1) B
end Tower
end YangMills.Construction
end
