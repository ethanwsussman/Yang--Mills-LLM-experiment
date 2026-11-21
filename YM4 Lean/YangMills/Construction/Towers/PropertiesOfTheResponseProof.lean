import YangMills.Construction.Towers.ExistenceOfTheBoundOfTheResponse
import YangMills.Construction.Towers.PropertiesOfTheResponse
import YangMills.Construction.Towers.TheFormulaForTheCoefficientsOfTheResponse
import YangMills.Construction.Towers.TheRelationsOfTheResponse
import YangMills.Construction.Towers.TheResponseNearZero
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower.ResponseProperties
theorem allProperties_holds (hRel : ResponseRelationsAtAllHeights.ResponseRelationsHold)
    (hCoeff : ResponseCoefficientFormula.Claim)
    (hBound : ResponseBoundExists)
    (hSmall : ResponseAtSmallMomentum.Statement) : AllProperties :=
  ⟨hRel, hCoeff, Classical.epsilon_spec hBound, hSmall⟩
end YangMills.Construction.Tower.ResponseProperties
