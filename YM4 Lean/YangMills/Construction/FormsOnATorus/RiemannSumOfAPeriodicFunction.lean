import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace YangMills.Construction.RiemannSums
def dualTorusMomentum {N : ℕ} (j : Fin 4 → ZMod N) : Fin 4 → ℝ := fun i => 2 * Real.pi * ((j i).valMinAbs : ℝ) / (N : ℝ)
def TendstoRiemannSumOfPeriodic : Prop :=
  ∀ (F : (Fin 4 → ℝ) → ℂ) (B : ℝ), Measurable F → (∀ p, ‖F p‖ ≤ B) →
    (∀ (i : Fin 4) (p : Fin 4 → ℝ), F (p + Pi.single i (2 * Real.pi)) = F p) →
    (∀ p : Fin 4 → ℝ, p ≠ 0 → (∀ i, -Real.pi ≤ p i ∧ p i ≤ Real.pi) → ContinuousAt F p) →
    Tendsto (fun n : ℕ => (((2 * (n + 1) : ℕ) : ℂ) ^ 4)⁻¹ *
        ∑ j : Fin 4 → ZMod (2 * (n + 1)), F (dualTorusMomentum j)) atTop
      (𝓝 (((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4 *
        ∫ p in Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), F p))
end YangMills.Construction.RiemannSums
end
