import YangMills.Construction.Lattice.BoxLaplacianLowerBound
import Mathlib
noncomputable section
namespace YangMills.Construction.Lattice.BoxSpectralGap
def boxLinkTerm {n N : ℕ} (g : (Fin n → Fin N) → ℝ) (σ : Fin n → Fin N) (i : Fin n) : ℝ :=
  if h : (σ i : ℕ) + 1 < N then (g (Function.update σ i ⟨σ i + 1, h⟩) - g σ) ^ 2 else 0
def boxDirichletEnergy {n N : ℕ} (g : (Fin n → Fin N) → ℝ) : ℝ := ∑ i, ∑ σ, boxLinkTerm g σ i
end YangMills.Construction.Lattice.BoxSpectralGap
