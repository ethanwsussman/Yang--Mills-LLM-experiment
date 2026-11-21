import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.RealFunctions
def AddInvStatement : Prop :=
  ((∃ e : Set.Ici (1 : ℝ) ≃ₜ Set.Ici (2 : ℝ),
      (∀ x : Set.Ici (1 : ℝ), (e x : ℝ) = (x : ℝ) + (x : ℝ)⁻¹) ∧ StrictMono e) ∧
    StrictMonoOn (fun x : ℝ => x - x⁻¹) (Set.Ici (1 : ℝ))) ∧
  (∀ w : ℂ, 2 ≤ ‖w + 1‖ + ‖w - 1‖ ∧
    (‖w + 1‖ + ‖w - 1‖ = 2 ↔ w ∈ (fun x : ℝ => (x : ℂ)) '' Set.Icc (-1 : ℝ) 1)) ∧
  (∀ w : ℂ, ∃! x : ℝ, x ∈ Set.Ici (1 : ℝ) ∧ x + x⁻¹ = ‖w + 1‖ + ‖w - 1‖)
end YangMills.Construction.RealFunctions
