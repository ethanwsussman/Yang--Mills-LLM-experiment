import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityOfACell
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def reflectedMeanBoundOnTwoCellTorus : Prop :=
  ForAllCeilings fun P Kr Ξ => ∃ A₀ b₀ : ℝ, 0 ≤ A₀ ∧ 0 ≤ b₀ ∧ ForAllSources P Kr Ξ fun β K κ c ρ H Λ f =>
    ∀ z : TorusFields.TorusSite (2 * P.side ^ κ), ReflectedMeanBounded P β K κ 2 z f (centring P β c K κ ρ f)
      (ReflectedCopies.copySize A₀ b₀ (cellLength P.side K κ) ρ * sourceNorm ρ H Λ)
end YangMills.Construction.SmallTorusCopies
end
