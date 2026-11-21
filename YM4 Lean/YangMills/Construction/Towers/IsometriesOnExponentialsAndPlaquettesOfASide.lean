import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def PeriodicSymmetriesActOnExpAndFaces : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    LeftChartAlgebra.SymmetryExpFace L n k j
end YangMills.Construction.Tower
end
