import YangMills.Construction.Towers.KernelsFieldsAndPropertiesOfTheTwoOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.TwoOperators
def AtTrivialField : Prop :=
  ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    AtIdentityOnLattice L ∧ (∀ n : ℕ, 0 < n → AtIdentityOnTorus L n) ∧ CoeffMapProperties L
end YangMills.Construction.Tower.TwoOperators
end
