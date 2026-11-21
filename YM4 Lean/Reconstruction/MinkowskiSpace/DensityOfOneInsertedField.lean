import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.InsertedFieldForm
def FieldDensityExists : Prop :=
  ∀ (sigma : TestSpaces.SepTuple → ℝ)
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma))
    (p C : ℝ), Hypotheses sigma E p C →
    ∃ G : ℝ → (Fin 4 → ℝ) → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma),
      IsFieldDensity sigma E G
end YangMills.Construction.InsertedFieldForm
end
