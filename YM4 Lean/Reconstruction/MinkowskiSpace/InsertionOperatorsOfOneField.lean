import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.InsertionOperators
def InsertionOperatorBounds : Prop :=
  ∀ (sigma : TestSpaces.SepTuple → ℝ)
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma))
    (p C : ℝ), InsertedFieldForm.Hypotheses sigma E p C →
    ∀ η : ℝ, 0 < η → η ≤ 1 →
      (∀ f : (Fin 4 → ℝ) → ℂ, InsertedFieldForm.IsAdmissible η f →
        InsertedFieldForm.IsInsertionOp sigma η f (InsertedFieldForm.insertionOp sigma η f) ∧
          OneLoopNotation.opNormOf (InsertedFieldForm.insertionOp sigma η f) ≤
            C * η ^ (-p) * WightmanReconstruction.supC1Norm f) ∧
      (∀ {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → (Fin 4 → ℝ) → ℂ) (D : Set (Fin 4 → ℝ)),
        (∀ i ∈ s, InsertedFieldForm.IsAdmissible η (f i)) → (∀ i ∈ s, tsupport (f i) ⊆ D) →
        (∀ x ∈ D, ∀ y ∈ D, TorusMetric.euclidNormVec (x - y) ≤ 1) →
          InsertedFieldForm.insertionOp sigma η (∑ i ∈ s, c i • f i) =
            ∑ i ∈ s, c i • InsertedFieldForm.insertionOp sigma η (f i)) ∧
      ∀ (f : (Fin 4 → ℝ) → ℂ) (a : Fin 4 → ℝ), InsertedFieldForm.IsAdmissible η f →
        0 ≤ a TimeAxis.timeIdx →
        InsertedFieldForm.IsAdmissible η (InsertedFieldForm.translateFun a f) →
          InsertedFieldForm.insertionOp sigma η (InsertedFieldForm.translateFun a f) *
              FieldForms.spectralTranslation E (InsertedFieldForm.realWickPoint a) =
            FieldForms.spectralTranslation E (InsertedFieldForm.realWickPoint a) *
              InsertedFieldForm.insertionOp sigma η f
end YangMills.Construction.InsertionOperators
end
