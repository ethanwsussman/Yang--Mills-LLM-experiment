import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def AnalyticFieldFunctionTendsAtOne : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    ∀ (U : Set (Tower.Edge L n k j → Matrices.ComplexMatrix2))
      (G : (Tower.Edge L n k j → Matrices.ComplexMatrix2) → ℝ),
      Tower.IsOpenNhdOfOne U → Tower.IsAnalyticFieldFunction U G →
        Tendsto G (𝓝[Tower.fieldSpace L n k j] fun _ => (1 : Matrices.ComplexMatrix2)) (𝓝 (G fun _ => 1))
end YangMills.Construction.RunningCouplingSlope
end
