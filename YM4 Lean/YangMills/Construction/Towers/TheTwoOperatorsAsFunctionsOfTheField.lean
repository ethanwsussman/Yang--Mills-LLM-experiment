import YangMills.Construction.Towers.KernelsFieldsAndPropertiesOfTheTwoOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def TwoOperatorsAsFieldFunctions : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → TwoOperators.CoeffMapProperties L
end YangMills.Construction.Tower
end
