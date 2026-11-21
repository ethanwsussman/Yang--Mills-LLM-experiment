import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.InsertedFieldForm
def KernelInsertionConjugation : Prop :=
  ∀ (sigma : TestSpaces.SepTuple → ℝ)
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma))
    (p C : ℝ), Hypotheses sigma E p C →
    ∀ (η : ℝ) (Γ : Finset (Fin 4)) (a : Fin 4 → ℝ), 0 < η → η ≤ 1 →
      |a TimeAxis.timeIdx| ≤ η / 2 →
      IsAdmissible η (translateFun ((2 * η) • FieldFormConditions.timeUnitVec + a) (scaledKernel η Γ)) ∧
      FieldForms.spectralTranslation E (FieldForms.imagTimeShift η) *
          insertionOp sigma η
            (translateFun ((2 * η) • FieldFormConditions.timeUnitVec + a) (scaledKernel η Γ)) *
          FieldForms.spectralTranslation E (FieldForms.imagTimeShift η) =
        conjKernelInsertion sigma E η Γ a
end YangMills.Construction.InsertedFieldForm
end
