import YangMills.Construction.Towers.TheTwoOperatorsAsFunctionsOfTheField
import YangMills.Construction.Towers.TheTwoOperatorsAtOneOnATorus
import YangMills.Construction.Towers.TheTwoOperatorsAtOneOnTheUnitLattice
import YangMills.Construction.Towers.TheTwoOperatorsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower.TwoOperators
theorem atTrivialField_holds (h₁ : TwoOperatorsAtIdentityLatticeClaim)
    (h₂ : TwoOperatorsAtIdentityTorusClaim)
    (h₃ : TwoOperatorsAsFieldFunctions) : AtTrivialField :=
  fun L hL => ⟨h₁ L hL, fun n hn => h₂ L hL n hn, h₃ L hL⟩
end YangMills.Construction.Tower.TwoOperators
