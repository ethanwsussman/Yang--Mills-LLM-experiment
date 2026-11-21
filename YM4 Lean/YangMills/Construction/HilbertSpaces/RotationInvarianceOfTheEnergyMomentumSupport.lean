import YangMills.Construction.HilbertSpaces.ReconstructionFromAPositiveFormDefs
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ComplexOrder InnerProductSpace
open YangMills.Construction.EuclideanBorel (Space pvmSupport)
open YangMills.Construction.FormsOperators (IsC0Semigroup IsStronglyContUnitaryRep UnitaryMap)
open YangMills.Construction.TimeAxisSymbols (timeAxisStabilizer)
open YangMills.Construction.SpectralTheory (UnboundedOp)
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction.RotationInvariantSupport
def Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : ℝ≥0 → E →L[ℂ] E) (A : UnboundedOp E) (G : Space 3 → UnitaryMap E E)
    (U : UnitaryMap E E) (g : timeAxisStabilizer),
    IsC0Semigroup T → IsSemigroupGenerator T A → IsNegLogOf A (T 1) →
    IsStronglyContUnitaryRep G →
    (∀ a s, toCLM (G a) * T s = T s * toCLM (G a)) →
    (∀ s, toCLM U * T s = T s * toCLM U) →
    (∀ a, toCLM U * toCLM (G a) =
      toCLM (G (rotateSpatial g a)) * toCLM U) →
    YangMills.Construction.FormsOperators.unitaryConjugate U A = A ∧
    rotateMomentum g '' pvmSupport (jointSpectralMeasure A G) =
      pvmSupport (jointSpectralMeasure A G)
end YangMills.Construction.PositiveFormReconstruction.RotationInvariantSupport
