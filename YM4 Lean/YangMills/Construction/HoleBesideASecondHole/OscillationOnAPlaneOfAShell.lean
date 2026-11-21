import YangMills.Construction.HoleBesideASecondHole.GaugeOnAnOrthantOfAShell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ShellSlices
open LatticeFractionalIntegration ShellOrthant
def shellSliceOscillationStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (l : ℝ) (o : Fin 4 → ℝ) (σ : Fin 4 → ℤ) (i : Fin 4) (τ : ℤ)
    (Y : Finset Lattice4) (f : Lattice4 → ℍ[ℝ]) (w : Lattice4 → ℝ) (E : ℝ),
    100 ≤ l → (∀ k, σ k = 1 ∨ σ k = -1 ∨ σ k = 0) → σ i = 0 → |(τ : ℝ) - o i| ≤ l / 2 →
    (∀ x, x ∈ Y ↔ IsInShellOrthant o l σ x ∧ x i = τ) → 0 ≤ E → (∀ x, 0 ≤ w x) →
    (∀ x ∈ Y, ∀ j, x + basisVector j ∈ Y → ‖f (x + basisVector j) - f x‖ ≤ w x) →
    ∑ x ∈ Y, w x ^ 4 ≤ E ^ 4 →
    ∀ x ∈ Y, ∀ y ∈ Y, ‖f x - f y‖ ^ 4 ≤ C * l * E ^ 4
end YangMills.Construction.ShellSlices
end
