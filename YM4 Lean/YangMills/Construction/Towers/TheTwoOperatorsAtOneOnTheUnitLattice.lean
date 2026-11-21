import YangMills.Construction.Towers.KernelsFieldsAndPropertiesOfTheTwoOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open TwoOperators
def TwoOperatorsAtIdentityLatticeClaim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → AtIdentityOnLattice L
end YangMills.Construction.Tower
end
