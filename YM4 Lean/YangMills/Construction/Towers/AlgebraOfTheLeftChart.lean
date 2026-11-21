import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LeftChartAlgebra
def AllConditionsHold : Prop :=
  InvTraceIdentity ∧ HalfTraceInPauliCoords ∧
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k →
    (∀ n : ℕ, 0 < n → OnPeriodic L n k j ∧ ActionAsFaceSumBase L n k) ∧
      OnFull L k j
end YangMills.Construction.Tower.LeftChartAlgebra
end
