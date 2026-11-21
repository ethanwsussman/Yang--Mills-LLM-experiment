import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityOfACell
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def sixteenCopyBoundForAdmissibleFlows : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∀ Ξ : ℝ, y + 2 * Tb.B ≤ Ξ → ∃ A₀ b₀ : ℝ, 0 ≤ A₀ ∧ 0 ≤ b₀ ∧
    ∀ D : ChessboardTori.ChessboardSetup, D.L = Tb.side →
    IsAdmissibleFlow (Tb.stepParameters y) Ξ D.β (D.K : ℕ) → ReflectedCopies.SixteenCopyBound D A₀ b₀
end YangMills.Construction.SmallTorusCopies
end
