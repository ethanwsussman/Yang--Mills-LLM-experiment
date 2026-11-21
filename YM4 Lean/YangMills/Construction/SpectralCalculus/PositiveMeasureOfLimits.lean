import YangMills.Construction.HilbertSpace.CommutingSemigroupGroupPairs
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
namespace YangMills.Construction.SpectralCalculus
def PositiveSpectralMeasureOfLimits : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : ℝ≥0 → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H) (v : ℕ → H) (g : ℝ≥0 → ℝ → ℂ),
    IsCommutingSemigroupGroup T U →
    (∀ t : ℝ≥0, 0 < t → (g t 0).im = 0) →
    (∀ t₀ : ℝ≥0, 0 < t₀ → ∀ (t : ℝ≥0) (s : ℝ),
      Tendsto (fun p : ℕ × ℕ => inner ℂ (T t₀ (v p.1)) (T t (U s (T t₀ (v p.2))))) atTop
        (𝓝 (g (2 * t₀ + t) s))) →
    ∃ ρ : Measure SpectralPlane, ∀ t : ℝ≥0, 0 < t →
      ∫⁻ p, ENNReal.ofReal (Real.exp (-(t : ℝ) * (p.1 : ℝ))) ∂ρ < ∞ ∧
        ∀ s : ℝ, g t s = ∫ p, spectralCharacter t s p ∂ρ
end YangMills.Construction.SpectralCalculus
end
