import YangMills.Construction.ClusterExpansionOfAStep.BasesAtABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
namespace TorusLumps
def MeasurableContourMeanStatement : Prop :=
  ∀ (ℓ : StepParameters) (n : ℕ) [NeZero n]
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) (f : ℍ[ℝ] → ℝ), Continuous f →
    Measurable fun W : TorusFields.TorusField (n * ℓ.side) =>
      f (LumpContours.contourMean ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ n W)) b
        (fineLevelField ℓ n W) c)
end TorusLumps
end YangMills.Construction
end
