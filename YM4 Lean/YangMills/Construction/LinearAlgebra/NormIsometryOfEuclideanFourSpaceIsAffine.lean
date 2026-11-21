import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LinearAlgebra.NormIsometry
def BijectiveNormIsometryIsAffine : Prop :=
  ∀ n : Seminorm ℝ (Fin 4 → ℝ), (∀ x, n x = 0 → x = 0) →
    ∀ f : (Fin 4 → ℝ) → Fin 4 → ℝ, Function.Bijective f →
      (∀ x y, n (f x - f y) = n (x - y)) →
        ∃ g : (Fin 4 → ℝ) →ᵃ[ℝ] (Fin 4 → ℝ), ⇑g = f
end YangMills.Construction.LinearAlgebra.NormIsometry
