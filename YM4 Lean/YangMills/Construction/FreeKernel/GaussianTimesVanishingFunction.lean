import YangMills.Construction.Constants.HeatKernelGaussianNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open MeasureTheory YangMills.Construction.Constants.HeatKernel
def VanishingTimesGaussianBound : Prop :=
  ∀ (n b : ℕ) (M t : ℝ) (I : Set ℝ) (ρ g : ℝ → ℂ),
    0 ≤ M → 1 ≤ t → I.OrdConnected →
    ContDiffOn ℝ n ρ I → ContDiffOn ℝ n g I →
    (∀ k : ℕ, k ≤ n → ∀ θ ∈ I,
      ‖iteratedDerivWithin k ρ I θ‖ ≤ M * |θ| ^ (b - k) ∧
      ‖iteratedDerivWithin k g I θ‖ₑ ≤
        weightedFactorialPower k *
          ENNReal.ofReal (t ^ ((k : ℝ) / 2) * Real.exp (-(heatDecay * t * θ ^ 2)))) →
    (∀ θ ∈ I,
      ‖iteratedDerivWithin n (fun x => ρ x * g x) I θ‖ₑ ≤
        ENNReal.ofReal M * binomialMoment n b *
          ENNReal.ofReal
            (t ^ (((n : ℝ) - b) / 2) * Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2)))) ∧
    ∫⁻ θ in I, ‖iteratedDerivWithin n (fun x => ρ x * g x) I θ‖ₑ ≤
      ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2)) * ENNReal.ofReal M * binomialMoment n b *
        ENNReal.ofReal (t ^ (((n : ℝ) - b - 1) / 2))
end YangMills.Construction.FreeKernel
