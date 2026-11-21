import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.MidpointSelfAdjoint
def MidpointSelfAdjointStatement : Prop :=
  ∀ (sigma : TestSpaces.SepTuple → ℝ)
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma))
    (p C : ℝ), InsertedFieldForm.Hypotheses sigma E p C →
    ∀ G : ℝ → (Fin 4 → ℝ) → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma),
      InsertedFieldForm.IsFieldDensity sigma E G →
      ∀ s : ℝ, 0 < s →
        HilbertToolkit.adjointOp (InsertedFieldForm.midpointField sigma G s) =
          InsertedFieldForm.midpointField sigma G s
end YangMills.Construction.MidpointSelfAdjoint
end
