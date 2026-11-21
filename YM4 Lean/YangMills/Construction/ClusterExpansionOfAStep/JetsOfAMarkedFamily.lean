import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.PolymerCumulant
def bondWeightedIntegral {α ι β : Type} [MeasurableSpace α] (μ : Measure α) {k : ℕ} (bonds : Finset ι → Finset β)
    (d : Finset ι → α → ℝ) (K : α → (Fin k → ℝ) → ℝ) (M : β → α → (Fin k → ℝ) → ℝ) (X : Finset ι)
    (x : Fin k → ℝ) : ℝ :=
  ∫ a, d X a * K a x * ∏ b ∈ bonds X, M b a x ∂μ
structure BondExpansion {α ι β : Type} [MeasurableSpace α] [DecidableEq ι] (μ : Measure α) {k : ℕ} (N : ℕ)
    (U : Set (Fin k → ℝ)) (x₀ : Fin k → ℝ) (block : β → ι) (all near : Finset β) (bonds : Finset ι → Finset β)
    (d : Finset ι → α → ℝ) (K : α → (Fin k → ℝ) → ℝ) (M : β → α → (Fin k → ℝ) → ℝ) (P Q₀ Q κ : ℝ) : Prop where
  isOpen : IsOpen U
  center_mem : x₀ ∈ U
  mem_bonds : ∀ X b, b ∈ bonds X ↔ b ∈ all ∧ block b ∈ X
  integral_pos : ∀ X, ∀ x ∈ U, 0 < bondWeightedIntegral μ bonds d K M X x
  integral_le_two_mul_insert : ∀ X Y, bondWeightedIntegral μ bonds d K M X x₀ ≤
    2 * bondWeightedIntegral μ bonds d K M (insert Y X) x₀
  weight_nonneg : ∀ X a, 0 ≤ d X a
  weight_antitone : ∀ X Z a, Z ⊆ X → d X a ≤ d Z a
  kernel_nonneg : ∀ a, ∀ x ∈ U, 0 ≤ K a x
  kernel_contDiffOn : ∀ a, ContDiffOn ℝ N (K a) U
  kernel_iteratedFDeriv_le : ∀ a, ∀ i ≤ N, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (K a) x‖ ≤ P ^ i * K a x
  kernel_le_center : ∀ a, ∀ x ∈ U, K a x ≤ κ * K a x₀
  mark_nonneg : ∀ b ∈ all, ∀ a, ∀ x ∈ U, 0 ≤ M b a x
  mark_le_one : ∀ b ∈ all, ∀ a, ∀ x ∈ U, M b a x ≤ 1
  mark_contDiffOn : ∀ b ∈ all, ∀ a, ContDiffOn ℝ N (M b a) U
  mark_iteratedFDeriv_le : ∀ b ∈ near, ∀ a, ∀ i, 1 ≤ i → i ≤ N → ∀ x ∈ U, ‖iteratedFDeriv ℝ i (M b a) x‖ ≤ Q
  mark_iteratedFDeriv_center_le : ∀ b ∈ near, ∀ a, ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv ℝ i (M b a) x₀‖ ≤ Q₀
  mark_eq_center : ∀ b ∈ all, b ∉ near → ∀ a, ∀ x ∈ U, M b a x = M b a x₀
  one_le_rate : 1 ≤ P
  one_le_centerBound : 1 ≤ Q₀
  one_le_markBound : 1 ≤ Q
def LogIteratedDerivBoundStatement : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 0 ≤ C ∧ ∀ {α ι β : Type} [MeasurableSpace α] [DecidableEq ι] (μ : Measure α) {k : ℕ}
    (U : Set (Fin k → ℝ)) (x₀ : Fin k → ℝ) (block : β → ι) (all near : Finset β) (bonds : Finset ι → Finset β)
    (d : Finset ι → α → ℝ) (K : α → (Fin k → ℝ) → ℝ) (M : β → α → (Fin k → ℝ) → ℝ) (P Q₀ Q κ : ℝ),
    BondExpansion μ N U x₀ block all near bonds d K M P Q₀ Q κ → ∀ X : Finset ι,
      ContDiffAt ℝ N (fun x => Real.log (bondWeightedIntegral μ bonds d K M X x)) x₀ ∧
      ‖iteratedFDeriv ℝ N (fun x => Real.log (bondWeightedIntegral μ bonds d K M X x)) x₀‖ ≤
        C * (((near.card : ℝ) + 1) * (2 * P * Q₀)) ^ N
end YangMills.Construction.PolymerCumulant
end
