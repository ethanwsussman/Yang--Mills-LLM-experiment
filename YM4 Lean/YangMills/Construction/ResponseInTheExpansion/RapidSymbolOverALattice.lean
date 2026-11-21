import Mathlib
set_option autoImplicit false
open scoped SchwartzMap
namespace YangMills.Construction.LatticeFourier
def schwartzLatticeSumDecayStatement : Prop :=
  ∀ f : 𝓢(Fin 4 → ℝ, ℂ), ∃ C : ℝ, ∀ (h : ℝ) (z : Fin 4 → ℝ) (i : Fin 4), 0 < h → h ≤ 1 → z i ≠ 0 →
    h * |z i| ≤ Real.pi →
    Summable (fun k : Fin 4 → ℤ =>
      f (fun j => h * k j) * Complex.exp (Complex.I * ((∑ j, h * k j * z j : ℝ) : ℂ))) ∧
    ‖(h : ℂ) ^ 4 * ∑' k : Fin 4 → ℤ,
      f (fun j => h * k j) * Complex.exp (Complex.I * ((∑ j, h * k j * z j : ℝ) : ℂ))‖ ≤
      C * (|z i| ^ 5)⁻¹
end YangMills.Construction.LatticeFourier
