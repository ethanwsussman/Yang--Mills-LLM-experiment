import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def ConvolutionRiemannSumSharpEstimates.Statement : Prop :=
  ∀ sc : FixedScale, ∀ k ∈ ccIn (univ : Set AmbientSpace), ∀ φ ∈ compactC1Complex, ∀ δ : ℝ,
    0 < δ →
      sc.sharpNorm (convolve k φ - cubeRiemannSum δ k φ) ≤
        l1Norm k * sc.translationModulus φ δ ∧
      sc.sharpNorm (cubeRiemannSum δ k φ) ≤ l1Norm k * sc.sharpNorm φ ∧
      sc.sharpNorm (convolve k φ) ≤ l1Norm k * sc.sharpNorm φ ∧
      ((∀ x, IsRealNonneg (k x)) → lebesgueIntegral k = 1 →
        tsupport k ⊆ euclidClosedBall (0 : AmbientSpace) δ →
        sc.sharpNorm (convolve k φ - φ) ≤ sc.translationModulus φ δ)
end YangMills.Construction.TwoPoints
end
