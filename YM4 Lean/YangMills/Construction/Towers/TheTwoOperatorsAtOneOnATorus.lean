import YangMills.Construction.Towers.KernelsFieldsAndPropertiesOfTheTwoOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def TwoOperatorsAtIdentityTorusClaim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m : ℕ, 0 < m →
    TwoOperators.AtIdentityOnTorus L m
end YangMills.Construction.Tower
end
