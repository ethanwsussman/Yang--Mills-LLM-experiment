import YangMills.Construction.Dirichlet.CrossingChainSumEstimate
import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
namespace YangMills.Construction.Torus
variable {d : ℕ} {S : ℝ}
theorem coe_int_mul_period (n : ℤ) : (((n : ℝ) * S : ℝ) : AddCircle S) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples_iff.2 ⟨n, by simp⟩)
theorem norm_coe_le_abs (x : ℝ) : ‖(x : AddCircle S)‖ ≤ |x| := by apply _root_.YangMills.Construction.TorusMetric.addCircle_norm_coe_le_abs <;> assumption
theorem exists_lift_abs_eq_norm (x : AddCircle S) : ∃ r : ℝ, (r : AddCircle S) = x ∧ |r| = ‖x‖ := by apply _root_.YangMills.Construction.TorusMetric.exists_coe_eq_abs_eq_norm <;> assumption
theorem supNorm_eq_norm (p : PeriodicTorus d S) : supNorm p = ‖p‖ := by
  have hb : BddBelow {r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = ‖v‖} :=
    ⟨0, by rintro _ ⟨v, -, rfl⟩; exact norm_nonneg v⟩
  choose r hr hn using fun μ => exists_lift_abs_eq_norm (p μ)
  apply le_antisymm
  · refine (csInf_le hb ⟨r, funext hr, rfl⟩).trans ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg p)).2 fun μ => ?_
    rw [Real.norm_eq_abs, hn]
    exact norm_le_pi_norm p μ
  · refine le_csInf ⟨_, r, funext hr, rfl⟩ ?_
    rintro _ ⟨v, rfl, rfl⟩
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun μ => ?_
    exact (norm_coe_le_abs (v μ)).trans (norm_le_pi_norm v μ)
theorem lOneNorm_eq_sum_norm (p : PeriodicTorus d S) : lOneNorm p = ∑ μ, ‖p μ‖ := by
  have hb : BddBelow {r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = ∑ μ, |v μ|} :=
    ⟨0, by rintro _ ⟨v, -, rfl⟩; exact Finset.sum_nonneg fun μ _ => abs_nonneg _⟩
  choose r hr hn using fun μ => exists_lift_abs_eq_norm (p μ)
  apply le_antisymm
  · refine (csInf_le hb ⟨r, funext hr, rfl⟩).trans ?_
    simp only [hn]
    exact le_rfl
  · refine le_csInf ⟨_, r, funext hr, rfl⟩ ?_
    rintro _ ⟨v, rfl, rfl⟩
    exact Finset.sum_le_sum fun μ _ => norm_coe_le_abs (v μ)
theorem lengthAxioms (d : ℕ) (S : ℝ) : LengthAxioms d S where
  lOneNorm_nonneg p := by
    rw [lOneNorm_eq_sum_norm]
    exact Finset.sum_nonneg fun μ _ => norm_nonneg _
  lOneNorm_zero := by simp [lOneNorm_eq_sum_norm]
  lOneNorm_neg p := by simp [lOneNorm_eq_sum_norm]
  lOneNorm_add_le p q := by
    simp only [lOneNorm_eq_sum_norm, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun μ _ => norm_add_le _ _
  supNorm_nonneg p := by
    rw [supNorm_eq_norm]
    exact norm_nonneg p
  supNorm_zero := by simp [supNorm_eq_norm]
  supNorm_le_lOneNorm p := by
    rw [supNorm_eq_norm, lOneNorm_eq_sum_norm]
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun μ _ => norm_nonneg _)).2 fun μ => ?_
    exact Finset.single_le_sum (f := fun μ => ‖p μ‖) (fun μ _ => norm_nonneg _) (Finset.mem_univ μ)
  lOneNorm_le_supNorm p := by
    rw [supNorm_eq_norm, lOneNorm_eq_sum_norm]
    calc ∑ μ, ‖p μ‖ ≤ ∑ _μ : Fin d, ‖p‖ := Finset.sum_le_sum fun μ _ => norm_le_pi_norm p μ
      _ = (d : ℝ) * ‖p‖ := by simp
  continuous_supNorm := by
    have : (supNorm : PeriodicTorus d S → ℝ) = fun p => ‖p‖ := funext supNorm_eq_norm
    rw [this]
    exact continuous_norm
  continuous_torusProj := continuous_pi fun μ => (AddCircle.continuous_mk' S).comp (continuous_apply μ)
  torusProj_surjective p := by
    choose r hr using fun μ => QuotientAddGroup.mk_surjective (p μ)
    exact ⟨r, funext hr⟩
  exists_near_lattice_point σ hσ p := by
    choose r hr using fun μ => QuotientAddGroup.mk_surjective (p μ)
    refine ⟨torusProj d S fun μ => ((round (r μ / σ) : ℤ) : ℝ) * σ, ⟨fun μ => round (r μ / σ), rfl⟩, ?_⟩
    rw [supNorm_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => ?_
    have hp : (p - torusProj d S fun μ => ((round (r μ / σ) : ℤ) : ℝ) * σ) μ =
        ((r μ - ((round (r μ / σ) : ℤ) : ℝ) * σ : ℝ) : AddCircle S) := by
      rw [AddCircle.coe_sub, hr μ]
      rfl
    rw [hp]
    refine (norm_coe_le_abs _).trans ?_
    have h := abs_sub_round (r μ / σ)
    have he : r μ - ((round (r μ / σ) : ℤ) : ℝ) * σ = (r μ / σ - round (r μ / σ)) * σ := by
      field_simp
    rw [he, abs_mul, abs_of_pos hσ]
    nlinarith
theorem summable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Summable fun z : ℤ => Real.exp (-a * |(z : ℝ)|) := by apply _root_.YangMills.Construction.Dirichlet.ChainSumEstimate.summable_exp_neg_mul_abs <;> assumption
end YangMills.Construction.Torus
