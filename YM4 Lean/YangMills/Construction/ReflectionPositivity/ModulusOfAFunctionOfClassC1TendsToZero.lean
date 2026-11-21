import YangMills.Construction.ReflectionPositivity.SharpNormAndModulusOfAFunctionOfClassC1
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
def SmoothModulusVanishes.Claim : Prop :=
  ∀ (D : MirrorData) (𝕜 : Type) [RCLike 𝕜] (E : Ambient) (M : ScaleParam)
    (f : compactC1 D 𝕜 E),
    gradSup f < ∞ ∧
    (∀ δ : ℝ≥0, gradOsc f δ ≤ 2 * gradSup f ∧
      2 * gradSup f < ∞) ∧
    Filter.Tendsto (gradOsc f) (nhds 0) (nhds 0) ∧
    Filter.Tendsto (smoothModulus M f) (nhds 0) (nhds 0)
end YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
end
