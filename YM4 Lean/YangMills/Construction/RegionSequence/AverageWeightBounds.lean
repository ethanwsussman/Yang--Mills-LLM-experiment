import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.RegionSequence.AverageWeights
import YangMills.Construction.RegionSequence.CubePartitions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RegionSequence.AverageWeightBounds
open Set
open Dirichlet Torus NestedRegions
theorem norm_apply_le_supNorm {S : ℝ} (p : PeriodicTorus 4 S) (μ : Fin 4) : ‖p μ‖ ≤ supNorm p := by
  have hne : {r | ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ r = ‖v‖}.Nonempty := by
    choose w hw _ using fun ν => TorusMetric.exists_coe_eq_abs_eq_norm (p ν)
    exact ⟨_, w, funext hw, rfl⟩
  refine le_csInf hne ?_
  rintro _ ⟨v, hv, rfl⟩
  have hμ : p μ = ((v μ : ℝ) : AddCircle S) := by rw [← hv]; rfl
  rw [hμ]
  exact (TorusMetric.addCircle_norm_coe_le_abs (v μ)).trans (by simpa using norm_le_pi_norm v μ)
theorem supNorm_le_of_forall {S r : ℝ} (hr : 0 ≤ r) (p : PeriodicTorus 4 S) (h : ∀ μ, ‖p μ‖ ≤ r) :
    supNorm p ≤ r := by
  choose w hw hw' using fun ν => TorusMetric.exists_coe_eq_abs_eq_norm (p ν)
  have hbdd : BddBelow {r | ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ r = ‖v‖} :=
    ⟨0, by rintro _ ⟨v, -, rfl⟩; exact norm_nonneg _⟩
  refine (csInf_le hbdd ⟨w, funext hw, rfl⟩).trans ?_
  exact (pi_norm_le_iff_of_nonneg hr).2 fun μ => by
    rw [Real.norm_eq_abs, hw']
    exact h μ
end YangMills.Construction.RegionSequence.AverageWeightBounds
