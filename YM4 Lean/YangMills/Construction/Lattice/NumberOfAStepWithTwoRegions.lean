import YangMills.Construction.Lattice.BlocksAndCorridors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice
namespace PeriodicLattice
variable {L m : ℕ}
theorem site_mem_cubeAround {j : ℤ} (y : Site L m j) : (y : FourTorus L m) ∈ cubeAround y := by
  have hzero : TorusMetric.supNormVec 0 = 0 := by simp [TorusMetric.supNormVec]
  have hbdd : BddBelow (TorusMetric.supNormVec ''
      (TorusMetric.torusProj (torusSide L m) ⁻¹' {(0 : FourTorus L m)})) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, _, rfl⟩
    exact (abs_nonneg (w 0)).trans (Finset.le_sup' (fun μ => |w μ|) (Finset.mem_univ 0))
  have hmem : (0 : ℝ) ∈ TorusMetric.supNormVec ''
      (TorusMetric.torusProj (torusSide L m) ⁻¹' {(0 : FourTorus L m)}) :=
    ⟨0, by funext μ; simp [TorusMetric.torusProj], hzero⟩
  have hmesh : 0 ≤ meshSize L j := zpow_nonneg (Nat.cast_nonneg L) _
  have hinf := csInf_le hbdd hmem
  simp only [cubeAround, Set.mem_ofPred_eq, sub_self, TorusMetric.torusSupNorm]
  linarith
end PeriodicLattice
end YangMills.Construction
end
