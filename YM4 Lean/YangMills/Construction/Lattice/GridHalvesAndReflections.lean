import YangMills.Construction.Lattice.RectangularGrids
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellGrid
variable {L : ℕ} {κ : ℤ}
def halfIndices (d : CellGrid L κ) (μ : Fin 4) (s : ZMod (d.counts μ)) : Set d.CellIndex :=
  {k | ∃ j : ℕ, j < d.counts μ / 2 ∧ k μ = s + (j : ZMod (d.counts μ))}
def reflectIndex (d : CellGrid L κ) (μ : Fin 4) (s : ZMod (d.counts μ)) (k : d.CellIndex) :
    d.CellIndex :=
  Function.update k μ (2 * s - 1 - k μ)
end YangMills.Construction.CellGrid
end
