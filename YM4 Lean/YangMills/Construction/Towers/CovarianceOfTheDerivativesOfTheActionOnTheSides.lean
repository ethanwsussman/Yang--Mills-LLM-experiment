import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower.LeftChartAlgebra
def DerivativeCovarianceOnPeriodic : Prop :=
  ∀ L m k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → j ≤ k →
    DerivativeCovariance L m k j
end YangMills.Construction.Tower.LeftChartAlgebra
