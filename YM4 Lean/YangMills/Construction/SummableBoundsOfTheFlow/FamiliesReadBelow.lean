import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FamilyNorms
open TorusLumps ColdStepAtMirrorFrames
def localFamilyNormStatement : Prop :=
  ∀ (ℓ : StepParameters) (t : ℕ) (ε ε₃ : ℝ) (h : LocalDensity), ℓ.Admissible →
    ℓ.n₁ = (ℓ.side : ℝ) ^ (1 / 640 : ℝ) →
    IsNormBoundedFamily ℓ ε ε₃ h →
      IsNormBoundedLocalFamily ℓ.side t ℓ.n₀ ℓ.threshold ℓ.weightRate ε ε₃ (localFamilyOfDensity h)
end YangMills.Construction.FamilyNorms
end
