import YangMills.Construction.EuclideanAnalysis.PowerStripAndGaussianCharacters
import Mathlib
open Filter Topology MeasureTheory
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanAnalysis.Strip
def GaussianDensityTransforms : Prop :=
  ∀ a : ℝ,
    (∀ v : ℝ, 0 < v →
      (∫ t : ℝ, gaussianDensity v a t) = 1 ∧
      (∀ q : ℝ, (∫ t : ℝ, (gaussianDensity v a t : ℂ) * Complex.exp (Complex.I * t * q)) =
        Complex.exp (Complex.I * a * q - v * (q : ℂ) ^ 2 / 2)) ∧
      (∀ t : ℝ, (1 / (2 * Real.pi) : ℂ) *
          (∫ q : ℝ, Complex.exp (Complex.I * a * q - v * (q : ℂ) ^ 2 / 2) *
            Complex.exp (-(Complex.I * t * q))) =
        (gaussianDensity v a t : ℂ))) ∧
    ∀ g : ℝ → ℂ, Continuous g → (∃ C : ℝ, ∀ t, ‖g t‖ ≤ C) →
      Tendsto (fun v : ℝ => ∫ t : ℝ, (gaussianDensity v a t : ℂ) * g t) (𝓝[>] 0) (𝓝 (g a))
end YangMills.Construction.EuclideanAnalysis.Strip
