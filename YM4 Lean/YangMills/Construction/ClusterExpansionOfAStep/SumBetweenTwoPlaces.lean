import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.DecayingPairSums
def DoubleSumBoundBySeparation : Prop :=
  ∀ (ι Y : Type) [Fintype ι] (β : ι → Y) (dist : Y → Y → ℝ) (P P' : Finset Y) (f g : ι → ℝ) (κ A W D : ℝ),
    (∀ y y', 0 ≤ dist y y') → (∀ y y', dist y y' = dist y' y) →
    (∀ y y' y'', dist y y'' ≤ dist y y' + dist y' y'') → 0 ≤ κ → 0 ≤ A → 0 ≤ W →
    (∀ y, ∑ b, Real.exp (-(κ / 2 * dist (β b) y)) ≤ W) → (∀ y ∈ P, ∀ y' ∈ P', D ≤ dist y y') →
    (∀ b, 0 ≤ f b) → (∀ b, 0 ≤ g b) →
    (∀ b, f b = 0 ∨ ∃ y ∈ P, f b ≤ A * Real.exp (-(2 * κ * dist (β b) y))) →
    (∀ b, g b = 0 ∨ ∃ y ∈ P', g b ≤ A * Real.exp (-(2 * κ * dist (β b) y))) →
    ∑ b, ∑ b', f b * Real.exp (-(κ * dist (β b) (β b'))) * g b' ≤
      A ^ 2 * W ^ 2 * min (P.card : ℝ) P'.card * Real.exp (-(κ * D / 2))
end YangMills.Construction.DecayingPairSums
end
