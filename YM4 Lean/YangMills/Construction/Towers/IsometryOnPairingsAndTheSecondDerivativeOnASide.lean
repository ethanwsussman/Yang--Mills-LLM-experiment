import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.SideSymmetryPairingHessian
def Statement : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    LeftChartAlgebra.SymmetryPairingHessian L n k j
end YangMills.Construction.Tower.SideSymmetryPairingHessian
end
