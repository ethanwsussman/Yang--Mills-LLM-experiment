import YangMills.Construction.Lattice.PeriodicLatticeForms
import Mathlib
noncomputable section
namespace YangMills.Construction.Lattice
def latticeBox {d : ℕ} (ℓ : Fin d → ℝ) (ε : ℝ) {d' : ℕ} (N : ℕ) (μs : Fin d' → Fin d)
    (x₀ : LatticeSite ℓ ε) : Set (LatticeSite ℓ ε) :=
  Set.range fun σ : Fin d' → Fin N => x₀ + ∑ i, (σ i : ℕ) • latticeStep ℓ ε (μs i)
end YangMills.Construction.Lattice
