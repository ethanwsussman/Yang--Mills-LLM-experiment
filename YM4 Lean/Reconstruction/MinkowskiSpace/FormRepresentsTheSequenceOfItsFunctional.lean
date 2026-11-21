import YangMills.Construction.Continuum.ReflectionPositivityOfASequenceWithTheValuesOfAFunctional
import Reconstruction.MinkowskiSpace.EuclideanFieldFormsAndWhatAFormRepresents
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RepresentedSequence
def Statement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (Ω : H)
    (T : ℝ → OneLoopNotation.BddOp H) (p C : ℝ),
    FieldForms.IsBoundedFieldForm P Ω T p C →
    ∀ (sigma : TestSpaces.SepTuple → ℝ) (S : ConfigSpace.FlatSequence),
      FieldForms.RepresentsFunctional P Ω T sigma → ConfigSpace.IsLinearFunctionalSeq S →
      ConfigSpace.IsContinuousSeq S →
      ReflectionPositivityFromValues.AgreesOnTensors sigma S →
      FieldForms.RepresentsSequence P Ω T S
end YangMills.Construction.RepresentedSequence
end
