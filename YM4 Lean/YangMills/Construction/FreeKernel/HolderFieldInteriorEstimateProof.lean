import YangMills.Construction.FreeKernel.HolderFieldInteriorConstants
import YangMills.Construction.FreeKernel.PoissonInteriorEstimatesProof
import YangMills.Construction.Conventions.PositiveConstant
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.FreeKernel.HolderFieldInterior
open YangMills.Construction.InfiniteLattice YangMills.Construction.LatticePoisson YangMills.Construction.FreeKernel
variable {d : ℕ} {ξ : ℝ}
theorem abs_le_supLength (v : Fin d → ℝ) (μ : Fin d) : |v μ| ≤ supLength v :=
  le_ciSup (f := fun μ => |v μ|) (Set.finite_range _).bddAbove μ
theorem supLength_le (hd : 0 < d) {v : Fin d → ℝ} {s : ℝ} (h : ∀ μ, |v μ| ≤ s) :
    supLength v ≤ s := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact ciSup_le h
theorem mem_gridCube_iff (hd : 0 < d) {x₀ x : GridSite d ξ} {s : ℝ} :
    x ∈ gridCube x₀ s ↔ ∀ μ, |(x : Fin d → ℝ) μ - (x₀ : Fin d → ℝ) μ| ≤ s := by
  constructor
  · intro h μ
    exact (abs_le_supLength _ μ).trans h
  · intro h
    exact supLength_le hd h
theorem gridLength_nonneg (y : GridSite d ξ) : 0 ≤ gridLength y := by apply _root_.YangMills.Construction.PoissonInterior.zero_le_gridLength <;> assumption
def siteOfInt (m : Fin d → ℤ) : GridSite d ξ := ⟨fun μ => (m μ : ℝ) * ξ, m, fun _ => rfl⟩
theorem support_comp_add_finite {G : GridSite d ξ → ℝ} (h : (Function.support G).Finite)
    (a : GridSite d ξ) : (Function.support fun z => G (z + a)).Finite := by
  have e : (Function.support fun z => G (z + a)) = (fun z => z + a) ⁻¹' Function.support G := rfl
  rw [e]
  exact h.preimage (add_left_injective a).injOn
end YangMills.Construction.FreeKernel.HolderFieldInterior
