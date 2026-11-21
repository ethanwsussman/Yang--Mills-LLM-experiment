import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps
namespace ColdStepAtMirrorFrames
def BoltzmannWeightEqFunctional : Prop :=
  ∀ (ℓ : StepParameters) (t : ℕ) (x : ℝ) (D : TorusFunctional) (f : LocalDensity), ℓ.Admissible → ColdExpansion ℓ t x D f →
    ∀ (F : BlockFrame), IsCubicTorusAbove ℓ.side t ℓ.n₀ F → ∀ W : F.GaugeField F.depth, IsSmallCurvature ℓ.threshold W →
      D (F.period F.depth 0) (trivialField _) * lowerBoltzmann ℓ.coupling x (localFamilyOfDensity f) (finiteCells F) W =
        D (F.period F.depth 0) (restrictToTorus _ W)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
