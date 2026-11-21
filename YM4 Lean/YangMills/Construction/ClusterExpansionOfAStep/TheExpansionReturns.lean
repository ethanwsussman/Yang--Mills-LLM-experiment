import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepReturn
open YangMills.Construction.TorusLumps
def ExpansionReturnsAt (ℓ : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (D : TorusFunctional), ℓ.y₁ ≤ x → HasExpansion ℓ t x D →
    ∃ x' : ℝ, (HasExpansion ℓ (t + 1) x' (kernelImage ℓ x D) ∧ |x' - x| ≤ 2 * ℓ.B) ∧
      ∀ (x'' : ℝ) (f'' : LocalDensity), ColdExpansion ℓ (t + 1) x'' (kernelImage ℓ x D) f'' → x'' = x'
end YangMills.Construction.StepReturn
end
