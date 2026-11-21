import YangMills.Construction.Lattice.InfiniteLatticeCalculus
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {d : ℕ} {ξ : ℝ}
def gridCube (x₀ : GridSite d ξ) (s : ℝ) : Set (GridSite d ξ) :=
  {x | supLength ((x - x₀ : GridSite d ξ) : Fin d → ℝ) ≤ s}
def cubeHolderSeminorm (x₀ : GridSite d ξ) (r σ : ℝ) (H : GridSite d ξ → ℝ) : ℝ≥0∞ :=
  ⨆ z ∈ gridCube x₀ r, ⨆ z' ∈ gridCube x₀ r, ⨆ _ : z ≠ z',
    ENNReal.ofReal ((r / l1Length ((z - z' : GridSite d ξ) : Fin d → ℝ)) ^ σ * |H z - H z'|)
def fieldHolderSeminorm (x₀ : GridSite d ξ) (r σ : ℝ) (F : GridField d ξ) : ℝ≥0∞ :=
  ⨆ μ, cubeHolderSeminorm x₀ r σ (F μ)
end YangMills.Construction.InfiniteLattice
