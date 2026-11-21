import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def AnalyticMapDifferentiableStatement : Prop :=
  ∀ L n k a b : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → a ≤ k → b ≤ k →
    ∀ (S : Set (Edge L n k a → Matrices.ComplexMatrix2))
      (f : (Edge L n k a → Matrices.ComplexMatrix2) → Edge L n k b → Matrices.ComplexMatrix2),
      IsAnalyticFieldMap S f → IsDifferentiableFieldMap S f
end Tower
end YangMills.Construction
end
