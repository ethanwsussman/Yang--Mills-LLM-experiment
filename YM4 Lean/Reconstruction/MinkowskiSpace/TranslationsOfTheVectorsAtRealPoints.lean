import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.RealPointVectors
def TranslationOfTestStatesStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (vac : H)
    (T : ℝ → OneLoopNotation.BddOp H) (p c : ℝ),
    FieldForms.IsBoundedFieldForm P vac T p c →
    ∀ (m : ℕ) (f : Motions.TensorVal ℂ m) (a : MinkowskiSpace.RealVec4),
      f ∈ WightmanReconstruction.schwartzOfOrder m →
      FieldForms.spectralTranslation P (MinkowskiSpace.toComplex a) (testState P vac T m f) =
        testState P vac T m (translateVal a f)
end YangMills.Construction.RealPointVectors
