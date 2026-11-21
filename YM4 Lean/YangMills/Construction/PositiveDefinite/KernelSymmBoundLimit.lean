import YangMills.Construction.PositiveDefinite.KernelOnSet
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ComplexOrder Topology
open Filter
namespace YangMills.Construction.PositiveDefinite.KernelSymmBound
def SymmBoundLimitProperties : Prop :=
  ∀ (X : Type),
    (∀ k : X → X → ℂ, KernelPosSemidefOnSet k →
      (∀ x y : X, k y x = conj (k x y) ∧ ((‖k x y‖ ^ 2 : ℝ) : ℂ) ≤ k x x * k y y) ∧
        ∀ x : X, k x x = 0 → ∀ y : X, k x y = 0) ∧
    ∀ (K : ℕ → X → X → ℂ) (k' : X → X → ℂ),
      (∀ n, 1 ≤ n → KernelPosSemidefOnSet (K n)) →
      (∀ x y : X, Tendsto (fun n => K n x y) atTop (𝓝 (k' x y))) →
      KernelPosSemidefOnSet k'
end YangMills.Construction.PositiveDefinite.KernelSymmBound
