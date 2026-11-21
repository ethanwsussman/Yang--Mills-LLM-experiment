import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps MeasureTheory
namespace ColdStepAtMirrorFrames
def HaarIntegralEqStepIntegral : Prop :=
  ∀ (L t n : ℕ) [NeZero (n * L)], Odd L → 2 ≤ n →
    ∀ (V : (torusFrame L t n).GaugeField (torusFrame L t n).top) (G : TorusField (n * L) → ℝ), Measurable G → (∀ W, 0 ≤ G W) →
    (∀ (γ : (torusFrame L t n).Site (torusFrame L t n).depth → UnitQuaternion),
      (∀ z, γ (cellCentre (torusFrame L t n).depth z) = 1) →
      ∀ X : (torusFrame L t n).GaugeField (torusFrame L t n).depth,
        G (restrictToTorus _ (gaugeTransform γ X)) = G (restrictToTorus _ X)) →
    ∫ W, G W ∂(fieldHaar (n * L)) =
      ∫ w : StepVariable (finiteCells (torusFrame L t n)),
        G (restrictToTorus _ (chartedField (stepCoordinates w) V)) * ∏ b, haarLogDensity (w b)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
