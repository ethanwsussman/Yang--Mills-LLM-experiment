import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def GaugeDirectionHessianClaim : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k →
    FullSpace.LeftChartAlgebra.HessianGaugeDirection L k j
end YangMills.Construction.Tower.FullSpace
end
