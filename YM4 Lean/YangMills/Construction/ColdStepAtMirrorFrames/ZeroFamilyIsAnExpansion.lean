import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ZeroFamilyIsRegular : Prop :=
  ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ), 0 ≤ E → 0 ≤ E₃ → IsRegularFamily L t n₀ σ δ E E₃ fun _ _ _ => 0
end YangMills.Construction.ColdStepAtMirrorFrames
end
