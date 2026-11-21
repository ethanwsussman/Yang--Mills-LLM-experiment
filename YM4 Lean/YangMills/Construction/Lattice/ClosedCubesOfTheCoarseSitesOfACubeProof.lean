import YangMills.Construction.Lattice.CubesOfASeparatedSequence
import YangMills.Construction.Torus.SeparatedSequenceOfACoarseRegion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice SeparatedSequences TorusMetric
namespace CubeCovering.CoarseSiteCubes
variable {L m : ℕ}
theorem torusSupNorm_le_iff {P r : ℝ} (x : Torus4 P) : torusSupNorm x ≤ r ↔ ∀ μ, ‖x μ‖ ≤ r := by
  have key : torusSupNorm x = Finset.univ.sup' Finset.univ_nonempty fun μ => ‖x μ‖ := by
    choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (x μ)
    have hcov : torusProj P b = x := funext hb
    have hbdd : BddBelow (supNormVec '' (torusProj P ⁻¹' {x})) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨v, -, rfl⟩
      exact (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
    apply le_antisymm
    · refine csInf_le hbdd ⟨b, hcov, ?_⟩
      simp [supNormVec, hb']
    · refine le_csInf ⟨_, b, hcov, rfl⟩ ?_
      rintro _ ⟨v, hv, rfl⟩
      have hv' : torusProj P v = x := hv
      refine Finset.sup'_le _ _ fun μ _ => ?_
      have h1 : ‖x μ‖ ≤ |v μ| := by
        rw [← hv']
        exact addCircle_norm_coe_le_abs (v μ)
      exact h1.trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ))
  rw [key, Finset.sup'_le_iff]
  simp
variable (C : CubeData L m)
include C in
theorem base_pos : (0 : ℝ) < L := by
  have := C.two_le_base
  exact_mod_cast (by omega : 0 < L)
theorem levelScale_pos (n : ℕ) : 0 < C.levelScale n := zpow_pos (base_pos C) _
theorem levelScale_succ (n : ℕ) : C.levelScale (n + 1) = (L : ℝ) * C.levelScale n := by
  have hL := (base_pos C).ne'
  simp only [CubeData.levelScale, SeparatedSequences.ScaleData.levelMesh]
  rw [show ((n + 1 : ℕ) : ℤ) - (C.scales.unitLevel : ℤ) = 1 + ((n : ℤ) - (C.scales.unitLevel : ℤ)) by
    push_cast; ring, zpow_add₀ hL, zpow_one]
theorem blockSize_pos : (0 : ℝ) < C.blockSize := by
  rw [CubeData.blockSize]
  have := base_pos C
  push_cast
  positivity
variable {C}
end CubeCovering.CoarseSiteCubes
end YangMills.Construction
end
