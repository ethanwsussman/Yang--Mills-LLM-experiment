import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.InsertedFieldForm
def SupportedBelow (v : Fin 4 → ℝ) (f : (Fin 4 → ℝ) → ℂ) : Prop :=
  f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) ∧
    ∀ x ∈ tsupport f, 0 < x TimeAxis.timeIdx ∧ x TimeAxis.timeIdx ≤ v TimeAxis.timeIdx
def InsertedStateProperties : Prop :=
  ∀ (sigma : TestSpaces.SepTuple → ℝ)
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma))
    (p C : ℝ), Hypotheses sigma E p C →
    (∀ (v : Fin 4 → ℝ) (f : (Fin 4 → ℝ) → ℂ) (F : ReflectionPositivity.TupleForm.PositiveSpan),
      SupportedBelow v f →
      SeparatedTuples.formalMul (WightmanReconstruction.complexTuple f)
          (ReflectionPositivity.FormProperties.shiftedSpan v F).1 ∈
        SeparatedTuples.spanIn TimeAxis.upperHalfSpace) ∧
    (∀ {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → (Fin 4 → ℝ) → ℂ) (v : Fin 4 → ℝ)
      (F : ReflectionPositivity.TupleForm.PositiveSpan), (∀ i ∈ s, SupportedBelow v (f i)) →
        insertedState sigma (∑ i ∈ s, c i • f i) v F = ∑ i ∈ s, c i • insertedState sigma (f i) v F) ∧
    (∀ (a v : Fin 4 → ℝ) (f : (Fin 4 → ℝ) → ℂ) (F : ReflectionPositivity.TupleForm.PositiveSpan),
      0 ≤ a TimeAxis.timeIdx → SupportedBelow v f →
        FieldForms.spectralTranslation E (realWickPoint a) (insertedState sigma f v F) =
          insertedState sigma (translateFun a f) (a + v) F) ∧
    ∀ (v w : Fin 4 → ℝ) (f : (Fin 4 → ℝ) → ℂ) (F : ReflectionPositivity.TupleForm.PositiveSpan),
      0 ≤ w TimeAxis.timeIdx → SupportedBelow v f →
        insertedState sigma f (v + w) F =
          insertedState sigma f v (ReflectionPositivity.FormProperties.shiftedSpan w F)
end YangMills.Construction.InsertedFieldForm
end
