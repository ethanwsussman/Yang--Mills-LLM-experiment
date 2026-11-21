import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
variable {L n k j : ℕ}
def CovDiffInjective (W : Edge L n k j → Matrices.ComplexMatrix2) : Prop :=
  ∀ l ∈ vertexFunctionSpace L n k j, covDiff W l = 0 → l = 0
end YangMills.Construction.Tower
end
