import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower.TwistExpansionOnTorus
def Claim : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    LeftChartAlgebra.TwistExpansion L n k j
end YangMills.Construction.Tower.TwistExpansionOnTorus
