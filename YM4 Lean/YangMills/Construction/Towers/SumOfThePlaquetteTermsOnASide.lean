import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LeftChartAlgebra
def FaceSumFiniteSide : Prop :=
  ∀ L m k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → j ≤ k →
    ActionAsFaceSum L m k j ∧ ActionAsFaceSumBase L m k
end YangMills.Construction.Tower.LeftChartAlgebra
end
