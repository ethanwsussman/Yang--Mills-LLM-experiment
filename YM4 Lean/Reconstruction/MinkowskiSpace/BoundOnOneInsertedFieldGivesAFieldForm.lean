import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InsertedFieldForm
def BoundedFieldFormOfInsertionBound : Prop :=
  ∀ sigma : TestSpaces.SepTuple → ℝ, TestSpaces.IsSepFunctional sigma →
    FieldFormConditions.IsSymmetricInvariant sigma → FieldFormConditions.PairingPosSemidef sigma →
    ∀ E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma),
    FieldFormConditions.IsTranslationMeasure sigma E →
    ∀ p C : ℝ, 0 ≤ p → 1 ≤ C → FieldFormConditions.InsertionBound sigma p C →
      ∃ A : ℝ → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma),
        HasInsertionIntegral sigma E A ∧
        (∀ B : ℝ → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma),
          HasInsertionIntegral sigma E B →
          ∀ s : ℝ, 0 < s → B s = A s) ∧
        FieldForms.IsBoundedFieldForm E (FieldFormConditions.vacuumState sigma) A
          (formExponent p) (formConstant p C) ∧
        HasTimeOrderedIntegral sigma E A ∧
        RepresentsEuclideanSchwinger sigma E A
end YangMills.Construction.InsertedFieldForm
end
