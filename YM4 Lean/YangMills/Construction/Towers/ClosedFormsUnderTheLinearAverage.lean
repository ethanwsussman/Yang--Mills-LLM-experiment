import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.LinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def LinearSmoothingOnClosedForms : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    (∀ ξ ∈ edgeFormSpace L n k i, ∀ ξ' ∈ edgeFormSpace L n k i,
      linearSmoothing L n k i (ξ - ξ') = linearSmoothing L n k i ξ - linearSmoothing L n k i ξ') ∧
    (∀ ξ ∈ edgeFormSpace L n k i, IsClosedEdgeForm ξ →
      IsClosedEdgeForm (linearSmoothing L n k i ξ)) ∧
    ∀ B ∈ edgeFormSpace L n k (i + 1), IsClosedEdgeForm B →
      ∃ ξ ∈ edgeFormSpace L n k i, IsClosedEdgeForm ξ ∧ linearSmoothing L n k i ξ = B ∧
        fineOnlyContourAverage L n k i ξ = 0
end Tower
end YangMills.Construction
end
