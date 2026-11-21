import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.RealPointInnerProducts
def Statement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (Ω : H)
    (T : ℝ → OneLoopNotation.BddOp H) (p C : ℝ),
    FieldForms.IsBoundedFieldForm P Ω T p C →
    ∀ (k m : ℕ) (g : Motions.TensorVal ℂ k) (f : Motions.TensorVal ℂ m),
      g ∈ WightmanReconstruction.schwartzOfOrder k → f ∈ WightmanReconstruction.schwartzOfOrder m →
        ⟪RealPointVectors.testState P Ω T k g, RealPointVectors.testState P Ω T m f⟫_ℂ =
          RealPointVectors.wightmanFunctional P Ω T (k + m)
            (HyperplaneReflection.tensorVal (RealPointVectors.starVal g) f)
end YangMills.Construction.RealPointInnerProducts
end
