import YangMills.Construction.Continuum.SchwartzTestsAndMollifiers
import YangMills.Construction.MinkowskiSpace.BoundedFieldForms
import YangMills.Construction.ReflectionPositivity.PropertiesOfTheFormOfAFunctional
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.FieldFormConditions
abbrev timeUnitVec : Fin 4 → ℝ := PeriodicLattice.coordVec TimeAxis.timeIdx
variable (S : TestSpaces.SepTuple → ℝ)
def pairing (F F' : ReflectionPositivity.TupleForm.PositiveSpan) : ℂ :=
  WightmanReconstruction.linearExtension S
    (SeparatedTuples.formalMul (ReflectionPositivity.TupleForm.reflectConj F) F'.1)
def toTupleFunctional (h : S TestSpaces.sepTupleNil = 1) : SeparatedTuples.TupleFunctional where
  toFun X := S (TupleLists.ofList X)
  map_nil := by
    rw [← TupleLists.toList_sepTupleNil, TupleLists.ofList_toList, h]
theorem pairing_eq_reflectionForm (h : S TestSpaces.sepTupleNil = 1) :
    pairing S = ReflectionPositivity.TupleForm.reflectionForm (toTupleFunctional S h) :=
  rfl
abbrev StateSpace : Type := ProjectionMeasures.FormQuotientCompletion (pairing S)
def stateOf (F : ReflectionPositivity.TupleForm.PositiveSpan) : StateSpace S :=
  ProjectionMeasures.quotientClass (pairing S) F
def vacuumState : StateSpace S := stateOf S ReflectionPositivity.FormProperties.unitSpan
def IsSymmetricInvariant : Prop :=
  WightmanReconstruction.IsPermutationInvariant S ∧
    ∀ r : Motions.RigidMotion, WightmanReconstruction.IsMotionInvariant S r
def PairingPosSemidef : Prop := SesquilinearForms.IsPosSemidefForm (pairing S)
structure IsTranslationMeasure
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (StateSpace S)) : Prop where
  isPVM : ProjectionMeasures.IsPVM E
  supportedOn : ProjectionMeasures.IsSupportedOn E WightmanTheory.closedFutureConeBorel
  translate_stateOf : ∀ (F : ReflectionPositivity.TupleForm.PositiveSpan) (a : Fin 4 → ℝ),
    0 ≤ a TimeAxis.timeIdx →
    FieldForms.spectralTranslation E (MinkowskiSpace.wickMap (MinkowskiSpace.toComplex a))
        (stateOf S F) =
      stateOf S (ReflectionPositivity.FormProperties.shiftedSpan a F)
def ExistsTranslationMeasure : Prop :=
  ∃ E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (StateSpace S),
    IsTranslationMeasure S E
def InsertionBound (p C : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η ≤ 1 →
    ∀ f : (Fin 4 → ℝ) → ℂ, f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) →
      (∀ x ∈ tsupport f, η ≤ x TimeAxis.timeIdx ∧ x TimeAxis.timeIdx ≤ 3 * η) →
      (∀ x ∈ tsupport f, ∀ y ∈ tsupport f, TorusMetric.euclidNormVec (x - y) ≤ 1) →
      ∀ (F : ReflectionPositivity.TupleForm.PositiveSpan)
        (h : SeparatedTuples.formalMul (WightmanReconstruction.complexTuple f)
            (ReflectionPositivity.FormProperties.shiftedSpan ((4 * η) • timeUnitVec) F).1 ∈
              SeparatedTuples.spanIn TimeAxis.upperHalfSpace),
        ‖stateOf S ⟨_, h⟩‖ ≤
          C * η ^ (-p) * WightmanReconstruction.supC1Norm f * ‖stateOf S F‖
def ExistsInsertionBound : Prop :=
  ∃ p C : ℝ, 0 ≤ p ∧ 1 ≤ C ∧ InsertionBound S p C
end YangMills.Construction.FieldFormConditions
end
