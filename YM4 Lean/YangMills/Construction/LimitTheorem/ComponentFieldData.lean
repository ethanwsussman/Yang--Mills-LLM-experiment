import YangMills.Construction.LimitTheorem.ConditionsAtGivenConstants
import YangMills.Construction.MinkowskiSpace.ConditionsOnAFunctionalForAFieldForm

namespace YangMills.Construction.LimitTheorem
open SeparatedTuples ReflectionPositivity.TupleForm

/-- Euclidean estimates on a component used for field reconstruction. -/
def ComponentFieldData (σ : TupleFunctional) : Prop :=
  ∃ C : ConditionConstants, 0 ≤ C.cE ∧ 0 ≤ C.CE ∧
    HilbertSpaceBasics.IsPosSemidef (reflectionForm σ) ∧
    TestSpaces.IsSepFunctional (evalOnMap σ) ∧
    (∀ v : InfiniteLattice.AmbientSpace, σ.IsInvariant (SeparatedTuples.translate v)) ∧
    IsO4InvariantFunctional σ ∧ σ.IsPermInvariant ∧ GrowthBound C σ ∧
    FieldFormConditions.PairingPosSemidef (evalOnMap σ) ∧
    FieldFormConditions.ExistsTranslationMeasure (evalOnMap σ) ∧
    FieldFormConditions.ExistsInsertionBound (evalOnMap σ) ∧ ComponentConditions.ClustersAtInfinity σ

end YangMills.Construction.LimitTheorem
