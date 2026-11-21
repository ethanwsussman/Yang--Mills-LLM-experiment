import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ConfigSpace
variable {n : ℕ}
def segmentSet (y x : Config n) : Set (Config n) :=
  {w | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ w = y + s • (x - y)}
def taylorBoundNearDiagonal : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ f ∈ flatSchwartzSet n, ∀ y ∈ diagonalSet n, ∀ (x : Config n)
    (β : MultiIndex n) (r : ℕ), 1 ≤ r →
    ENNReal.ofReal ‖iteratedPartial β f x‖ ≤
        ENNReal.ofReal ((4 * (n : ℝ)) ^ r / (r.factorial : ℝ) * euclidNorm (x - y) ^ r) *
          ⨆ (w : Config n) (_ : w ∈ segmentSet y x) (γ : MultiIndex n)
            (_ : MultiIndex.order γ = r),
            ENNReal.ofReal ‖iteratedPartial (β + γ) f w‖ ∧
    ∀ δ : ℝ, 0 < δ → euclidNorm (x - y) ≤ δ → ∀ m : ℕ,
      ENNReal.ofReal ((1 + euclidNorm x) ^ m * ‖iteratedPartial β f x‖) ≤
        ENNReal.ofReal ((1 + δ) ^ m * ((4 * (n : ℝ) * δ) ^ r / (r.factorial : ℝ))) *
          decaySeminorm m (MultiIndex.order β + r) f
end YangMills.Construction.ConfigSpace
end
