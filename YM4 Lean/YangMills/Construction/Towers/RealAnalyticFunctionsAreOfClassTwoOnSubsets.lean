import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
def AnalyticIsC2OnSubsetsStatement : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    ∀ [Fintype (PositiveEdge L n k j)] (S A : Set (Edge L n k j → Matrices.ComplexMatrix2))
      (g : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ),
      IsAnalyticFieldFunction S g → A ⊆ S →
        Matrices.EmbeddedSubmanifold.IsC2OnCharted (restrictToPositiveEdges '' A)
          fun w => g (fieldOfPositiveValues w)
end YangMills.Construction.Tower
end
