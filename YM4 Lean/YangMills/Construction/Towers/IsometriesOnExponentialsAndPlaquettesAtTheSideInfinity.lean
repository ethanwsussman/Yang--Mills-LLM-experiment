import YangMills.Construction.Towers.LeftChartTranslationAlgebraFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def SymmetriesActOnExpAndFaces : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k →
    LeftChartAlgebra.SymmetryExpFace L k j
end YangMills.Construction.Tower.FullSpace
end
