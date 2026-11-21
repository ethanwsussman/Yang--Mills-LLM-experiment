import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.LeftChartAlgebra
def SymmetriesPreservePairingsAndHessian : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k → SymmetryPairingHessian L k j
end YangMills.Construction.Tower.FullSpace.LeftChartAlgebra
end
