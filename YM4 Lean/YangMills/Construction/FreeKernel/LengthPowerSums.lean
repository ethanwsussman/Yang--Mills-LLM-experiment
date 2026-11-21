import YangMills.Construction.Lattice.InfiniteLatticeCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open InfiniteLattice
def innerPowerTerm (d : ℕ) (ξ σ s : ℝ) : GridSite d ξ → ℝ :=
  Set.indicator {z : GridSite d ξ | 0 < l1Length (z : Fin d → ℝ) ∧ l1Length (z : Fin d → ℝ) ≤ s}
    (fun z => ξ ^ d * l1Length (z : Fin d → ℝ) ^ (-(d : ℝ) + σ))
def outerPowerTerm (d : ℕ) (ξ σ s : ℝ) : GridSite d ξ → ℝ :=
  Set.indicator {z : GridSite d ξ | s < l1Length (z : Fin d → ℝ)}
    (fun z => ξ ^ d * l1Length (z : Fin d → ℝ) ^ (-(d : ℝ) - 1 + σ))
def LengthPowerSumBounds : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ ξ σ : ℝ, 0 < ξ → 0 < σ → σ < 1 → ∀ s : ℝ, 0 < s →
    (Summable (innerPowerTerm d ξ σ s) ∧
      ∑' z, innerPowerTerm d ξ σ s z ≤ (6 : ℝ) ^ d * s ^ σ / ((2 : ℝ) ^ σ - 1)) ∧
    (Summable (outerPowerTerm d ξ σ s) ∧
      ∑' z, outerPowerTerm d ξ σ s z ≤ (6 : ℝ) ^ d * s ^ (σ - 1) / (1 - (2 : ℝ) ^ (σ - 1)))
end YangMills.Construction.FreeKernel
