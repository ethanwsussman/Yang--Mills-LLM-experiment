import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.TorusLumps
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ColdExpansionRegular : Prop :=
  ∀ (ℓ : YangMills.Construction.TorusLumps.StepParameters) (t : ℕ) (x : ℝ) (D : TorusFunctional)
    (f : LocalDensity), ℓ.Admissible →
    ℓ.n₁ = (ℓ.side : ℝ) ^ (1 / 640 : ℝ) → ColdExpansion ℓ t x D f →
    IsRegularFamily ℓ.side t ℓ.n₀ ℓ.threshold ℓ.weightRate ℓ.E ℓ.E₃ (localFamilyOfDensity f)
end YangMills.Construction.ColdStepAtMirrorFrames
end
