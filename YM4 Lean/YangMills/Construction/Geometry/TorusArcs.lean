import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction
namespace TorusArcs
variable (L m K u : ℕ)
variable {L m K u}
theorem torusSupNorm_eq_norm (x : FourTorus L m) : torusSupNorm x = ‖x‖ := by
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  have hcov : torusProj (torusSide L m) b = x := funext hb
  have hnn : ∀ v : Fin 4 → ℝ, 0 ≤ TorusMetric.supNormVec v := fun v =>
    (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
  apply le_antisymm
  · have hle : torusSupNorm x ≤ TorusMetric.supNormVec b := by
      refine csInf_le ⟨0, ?_⟩ ⟨b, hcov, rfl⟩
      rintro _ ⟨v, -, rfl⟩
      exact hnn v
    refine hle.trans (Finset.sup'_le _ _ fun μ _ => ?_)
    rw [hb']
    exact norm_le_pi_norm x μ
  · refine le_csInf ⟨_, b, hcov, rfl⟩ ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' : torusProj (torusSide L m) v = x := hv
    refine (pi_norm_le_iff_of_nonneg (hnn v)).2 fun μ => ?_
    rw [← hv']
    exact (addCircle_norm_coe_le_abs (v μ)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ))
variable (L m K u)
variable {L m K u}
variable (L m K u)
end TorusArcs
end YangMills.Construction
end
