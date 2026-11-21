import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Multilinear
def MultilinearTelescopingBound : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∀ (V : Fin n → Type) [∀ l, AddCommGroup (V l)] [∀ l, Module ℝ (V l)]
    (p : ∀ l, Seminorm ℝ (V l)) (c : ℝ), 0 ≤ c →
  ∀ Ψ : MultilinearMap ℝ V ℝ,
    (∀ h : ∀ l, V l, |Ψ h| ≤ c * ∏ l, p l (h l)) →
  ∀ f g : ∀ l, V l,
    |Ψ f - Ψ g| ≤
        c * ∑ l, p l (f l - g l) * (∏ l' ∈ Finset.Iio l, p l' (g l')) *
          ∏ l' ∈ Finset.Ioi l, p l' (f l') ∧
      c * ∑ l, p l (f l - g l) * (∏ l' ∈ Finset.Iio l, p l' (g l')) *
          ∏ l' ∈ Finset.Ioi l, p l' (f l') ≤
        c * ∑ l, p l (f l - g l) * ∏ l' ∈ Finset.univ.erase l, (p l' (f l') + p l' (g l'))
end YangMills.Construction.Multilinear
