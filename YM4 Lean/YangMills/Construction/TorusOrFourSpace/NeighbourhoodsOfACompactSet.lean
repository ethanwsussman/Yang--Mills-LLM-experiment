import YangMills.Construction.TorusOrFourSpace.SpaceQuotientMapAndDistance
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind)
def openThickening (K : Set (E.Pt D)) (_hK : IsCompactQ D E K) (η : ℝ) (_hη : 0 < η) :
    Set (E.Pt D) :=
  {y | infDistPt D E y K < ENNReal.ofReal η}
def closedThickening (K : Set (E.Pt D)) (_hK : IsCompactQ D E K) (η : ℝ) (_hη : 0 < η) :
    Set (E.Pt D) :=
  {y | infDistPt D E y K ≤ ENNReal.ofReal η}
end YangMills.Construction.PeriodicSpace.Kind
