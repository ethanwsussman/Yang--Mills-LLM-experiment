import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.MidpointOperators
def MidpointOperatorFacts : Prop :=
  ∀ (sigma : TestSpaces.SepTuple → ℝ)
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma))
    (p C : ℝ), InsertedFieldForm.Hypotheses sigma E p C →
    ∀ G : ℝ → (Fin 4 → ℝ) → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma),
      InsertedFieldForm.IsFieldDensity sigma E G →
      (∀ s a : ℝ, 0 < s → 0 < a →
        FieldForms.spectralTranslation E (FieldForms.imagTimeShift a) *
            InsertedFieldForm.midpointField sigma G s *
            FieldForms.spectralTranslation E (FieldForms.imagTimeShift a) =
          InsertedFieldForm.midpointField sigma G (s + a)) ∧
      (∀ s : ℝ, 0 < s →
        OneLoopNotation.opNormOf (InsertedFieldForm.midpointField sigma G s) ≤
          InsertedFieldForm.formConstant p C * min 1 s ^ (-InsertedFieldForm.formExponent p)) ∧
      ∀ (c s : ℝ) (y : Fin 4 → ℝ), 0 < s → s ≤ y TimeAxis.timeIdx →
        s ≤ c - y TimeAxis.timeIdx →
          G c y = FieldForms.spectralTranslation E
              (InsertedFieldForm.realWickPoint (y - s • FieldFormConditions.timeUnitVec)) *
            InsertedFieldForm.midpointField sigma G s *
              FieldForms.spectralTranslation E
                (InsertedFieldForm.realWickPoint ((c - s) • FieldFormConditions.timeUnitVec - y))
end YangMills.Construction.MidpointOperators
end
