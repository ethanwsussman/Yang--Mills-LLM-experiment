import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityOfACell
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def copyInequalityForAdmissibleFlows : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∀ Ξ : ℝ, y + 2 * Tb.B ≤ Ξ → ∃ A b : ℝ, 1 ≤ A ∧ 1 ≤ b ∧
    ∀ D : ChessboardTori.ChessboardSetup, D.L = Tb.side →
    IsAdmissibleFlow (Tb.stepParameters y) Ξ D.β (D.K : ℕ) → ReflectedCopies.CopyInequality D A b
end YangMills.Construction.SmallTorusCopies
end
