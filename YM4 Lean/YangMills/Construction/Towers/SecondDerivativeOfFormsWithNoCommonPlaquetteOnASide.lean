import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LeftChartAlgebra
def HessianDisjointVanishFiniteSide : Prop :=
  ∀ L m k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → j ≤ k →
    HessianDisjointVanish L m k j
end YangMills.Construction.Tower.LeftChartAlgebra
end
