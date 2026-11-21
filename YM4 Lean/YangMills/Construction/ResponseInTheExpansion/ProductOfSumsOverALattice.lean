import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LatticeFourier
def tsum_pi_prod_statement : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (n : ℕ) (f : Fin n → ℤ → 𝕜), (∀ i, Summable fun m => ‖f i m‖) →
    Summable (fun k : Fin n → ℤ => ‖∏ i, f i (k i)‖) ∧
      HasSum (fun k : Fin n → ℤ => ∏ i, f i (k i)) (∏ i, ∑' m, f i m)
end YangMills.Construction.LatticeFourier
