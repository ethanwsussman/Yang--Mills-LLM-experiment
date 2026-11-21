import YangMills.Construction.LimitTheorem.FunctionalDefs
import YangMills.Construction.MinkowskiSpace.ConditionsOnAFunctionalForAFieldForm
import YangMills.Construction.SystemsWithFiveBounds.InsertionConditionsOnConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
def ExistsInsertionBoundOfFieldOperatorBound : Prop :=
  ∀ (L : ℕ) (M : ℝ) (N : BoundConstants) (ς : SeparatedTuples.TupleFunctional), N.Admissible →
    FieldFormConditions.PairingPosSemidef (LimitTheorem.evalOnMap ς) →
    FieldOperatorBound L M N ς →
    FieldFormConditions.ExistsInsertionBound (LimitTheorem.evalOnMap ς)
end YangMills.Construction.SystemsWithFiveBounds
end
