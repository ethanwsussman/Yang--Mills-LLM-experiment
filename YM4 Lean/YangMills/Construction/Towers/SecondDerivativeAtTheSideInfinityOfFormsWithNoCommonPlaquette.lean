import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def FullSpaceHessianDisjointVanishes : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k →
    FullSpace.LeftChartAlgebra.HessianDisjointVanish L k j
end YangMills.Construction.Tower
end
