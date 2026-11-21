import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeCells
def unitCell {N p : ℕ} [NeZero N] (z : Fin p → Fin 4 → ZMod N) : Set (Fin p → Fin 4 → ℝ) :=
  Set.pi Set.univ fun i => Set.pi Set.univ fun μ => Set.Ico ((z i μ).val : ℝ) ((z i μ).val + 1)
def IntegralNearCellSum : Prop :=
  ∀ (N p : ℕ) [NeZero N] (F : (Fin p → Fin 4 → ℝ) → ℝ) (Gz : (Fin p → Fin 4 → ZMod N) → ℝ)
    (D : Finset (Fin p → Fin 4 → ZMod N)) (ε : ℝ),
    Measurable F → 0 ≤ ε → (∀ z ∈ D, ∀ u ∈ unitCell z, |F u - Gz z| ≤ ε) →
    (∀ z, z ∉ D → ∀ u ∈ unitCell z, F u = 0) →
    |(∫ u in Set.pi Set.univ (fun _ : Fin p => Set.pi Set.univ fun _ : Fin 4 => Set.Ico (0 : ℝ) N), F u) - ∑ z ∈ D, Gz z| ≤
      ε * D.card
end YangMills.Construction.LatticeCells
end
