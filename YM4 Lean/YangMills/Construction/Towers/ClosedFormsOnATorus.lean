import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.FormsOnTowers
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
namespace Tower
def ClosedEdgeFormsOnPeriodicLattice : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    ∀ B ∈ edgeFormSpace L n k j, IsClosedEdgeForm B ↔
      ∃ l ∈ vertexFunctionSpace L n k j, ∃ a ∈ edgeFormSpace L n k j,
        IsTranslationInvariantEdgeForm a ∧ B = vertexCoboundary l + a
end Tower
end YangMills.Construction
