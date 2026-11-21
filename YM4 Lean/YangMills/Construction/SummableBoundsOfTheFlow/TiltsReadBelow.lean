import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusLumps ColdStepAtMirrorFrames
namespace FamilyNorms
def vanishingFormLocalFamilyStatement : Prop :=
  ∀ (ℓ : StepParameters) (t : ℕ) (ε ε₃ : ℝ) (h : LocalDensity), ℓ.Admissible →
    ℓ.n₁ = (ℓ.side : ℝ) ^ (1 / 640 : ℝ) →
    IsNormBoundedFamily ℓ ε ε₃ h → HasVanishingCurvatureForm h →
    IsRegularFamily ℓ.side t ℓ.n₀ ℓ.threshold ℓ.weightRate ε ε₃ (localFamilyOfDensity h)
end FamilyNorms
end YangMills.Construction
end
