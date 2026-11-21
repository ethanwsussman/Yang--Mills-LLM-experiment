import YangMills.Construction.PositiveDefinite.KernelOnSet
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ComplexOrder Topology
open Filter
namespace YangMills.Construction.PositiveDefinite.KernelRestrictPullback
def RestrictPullbackScaleLimit : Prop :=
  ∀ (S : Type),
    (∀ k : S → S → ℂ, KernelPosSemidefOnSet k →
      (∀ x y : S, k y x = conj (k x y)) ∧
      (∀ x y : S, ((‖k x y‖ ^ 2 : ℝ) : ℂ) ≤ k x x * k y y) ∧
      (∀ x : S, k x x = 0 → ∀ y : S, k x y = 0) ∧
      (∀ T : Set S, KernelPosSemidefOnSet (fun x y : T => k x y)) ∧
      (∀ (R : Type) (g : R → S),
        KernelPosSemidefOnSet (fun x y : R => k (g x) (g y))) ∧
      (∀ c : ℝ, 0 < c → KernelPosSemidefOnSet (fun x y : S => (c : ℂ) * k x y))) ∧
    ∀ (K : ℕ → S → S → ℂ) (k' : S → S → ℂ),
      (∀ n, KernelPosSemidefOnSet (K n)) →
      (∀ x y : S, Tendsto (fun n => K n x y) atTop (𝓝 (k' x y))) →
      KernelPosSemidefOnSet k'
end YangMills.Construction.PositiveDefinite.KernelRestrictPullback
