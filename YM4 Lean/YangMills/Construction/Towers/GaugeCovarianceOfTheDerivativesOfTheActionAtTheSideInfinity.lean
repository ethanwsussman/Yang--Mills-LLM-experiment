import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ActionDerivativeCovariance
def Claim : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k →
    LeftChartAlgebra.DerivativeCovariance L k j
end YangMills.Construction.Tower.FullSpace.ActionDerivativeCovariance
end
