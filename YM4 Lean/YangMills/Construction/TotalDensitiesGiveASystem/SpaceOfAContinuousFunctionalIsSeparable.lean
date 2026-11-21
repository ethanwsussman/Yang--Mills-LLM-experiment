import YangMills.Construction.ReflectionPositivity.ReconstructionOfAFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
def PhysicalSpaceSeparable : Prop :=
  ∀ (σ : SeparatedTuples.TupleFunctional)
    (hσ : HilbertSpaceBasics.IsPosSemidef (ReflectionPositivity.TupleForm.reflectionForm σ)),
    σ.IsAdmissiblyContinuous →
    TopologicalSpace.SeparableSpace (ReflectionPositivity.Reconstruction.PhysicalSpace σ hσ)
end YangMills.Construction.TotalDensitiesGiveASystem
end
