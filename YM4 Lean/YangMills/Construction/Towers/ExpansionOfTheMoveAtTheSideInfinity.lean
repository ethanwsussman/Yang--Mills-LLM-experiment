import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def FullSpaceTwistExpansionClaim : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k →
    FullSpace.LeftChartAlgebra.TwistExpansion L k j
end YangMills.Construction.Tower
end
