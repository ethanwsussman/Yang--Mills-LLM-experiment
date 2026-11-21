import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Lattice.BoxLaplacianGap
def boxDirichletEnergy (N : ℕ) (g : (Fin 4 → Fin N) → ℝ) : ℝ :=
  ∑ μ : Fin 4, ∑ k : Fin 4 → Fin N,
    if h : (k μ : ℕ) + 1 < N then
      (g (Function.update k μ ⟨(k μ : ℕ) + 1, h⟩) - g k) ^ 2
    else 0
def BoxLaplacianSpectralGap : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    (∀ g : (Fin 4 → Fin N) → ℝ, ∑ k, g k = 0 →
      4 * Real.sin (Real.pi / (2 * (N : ℝ))) ^ 2 * ∑ k, g k ^ 2 ≤
        boxDirichletEnergy N g) ∧
    4 ≤ 4 * (N : ℝ) ^ 2 * Real.sin (Real.pi / (2 * (N : ℝ))) ^ 2 ∧
    4 * (N : ℝ) ^ 2 * Real.sin (Real.pi / (2 * (N : ℝ))) ^ 2 < Real.pi ^ 2
end YangMills.Construction.Lattice.BoxLaplacianGap
end
