import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def TranslationModulusProperties.Statement : Prop :=
  ∀ sc : FixedScale, ∀ f ∈ compactC1Complex,
    (TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f ∧
      TestFunctions.lipConstR4 f ≤ gradSup f ∧
      gradSupENN f < ∞ ∧
      (∀ δ : ℝ, 0 ≤ δ → gradOscENNReal f δ < ∞) ∧
      (∀ v v' : AmbientSpace, sc.sharpNorm (translateFun v f - translateFun v' f) ≤
        sc.translationModulus f (euclidNorm (v - v'))) ∧
      Tendsto (sc.translationModulus f) (𝓝[>] 0) (𝓝 0)) ∧
    MonotoneOn (sc.translationModulus f) (Ici 0)
end YangMills.Construction.TwoPoints
end
