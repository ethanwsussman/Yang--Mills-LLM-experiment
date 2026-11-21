import YangMills.Construction.LimitTheorem.RotationsAndTheConeOnOneCompletion
import YangMills.Construction.MinkowskiSpace.ConditionsOnAFunctionalForAFieldForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitTheorem
open SeparatedTuples ReflectionPositivity.TupleForm ReflectionPositivity.ReconstructionComplements
open HilbertSpaceBasics (IsPosSemidef)
open RotationsAndCone (spacelikeRegion isOpen_spacelikeRegion)
def TranslationMeasureFromReconstruction : Prop :=
  ∀ (ω : TupleFunctional) (h : IsPosSemidef (reflectionForm ω)),
    TestSpaces.IsSepFunctional (evalOnMap ω) → HasReconstruction ω h → SupportClaim ω h →
    jointMeasure ω h ⟨spacelikeRegion, isOpen_spacelikeRegion.measurableSet⟩ = 0 →
    FieldFormConditions.PairingPosSemidef (evalOnMap ω) ∧
      FieldFormConditions.ExistsTranslationMeasure (evalOnMap ω)
end YangMills.Construction.LimitTheorem
end
