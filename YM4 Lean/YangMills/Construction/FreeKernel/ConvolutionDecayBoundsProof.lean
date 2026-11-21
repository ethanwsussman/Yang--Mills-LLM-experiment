import YangMills.Construction.Lattice.InfiniteLatticeCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.ConvDecay
open InfiniteLattice
variable {d : ℕ} {ξ : ℝ}
abbrev siteNorm (z : GridSite d ξ) : ℝ := l1Length (z : Fin d → ℝ)
theorem siteNorm_nonneg (z : GridSite d ξ) : 0 ≤ siteNorm z :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem siteNorm_add_le (a b : GridSite d ξ) : siteNorm (a + b) ≤ siteNorm a + siteNorm b := by
  simp only [siteNorm, l1Length, AddSubgroup.coe_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun μ _ => abs_add_le _ _
theorem siteNorm_neg (a : GridSite d ξ) : siteNorm (-a) = siteNorm a := by
  simp [siteNorm, l1Length]
theorem siteNorm_sub_comm (a b : GridSite d ξ) : siteNorm (a - b) = siteNorm (b - a) := by
  rw [← neg_sub, siteNorm_neg]
theorem siteNorm_sub_le (a b c : GridSite d ξ) :
    siteNorm (a - c) ≤ siteNorm (a - b) + siteNorm (b - c) := by
  have h := siteNorm_add_le (a - b) (b - c)
  rwa [sub_add_sub_cancel] at h
end YangMills.Construction.FreeKernel.ConvDecay
