import YangMills.Construction.Dirichlet.CommutatorBoundsProof
import YangMills.Construction.Dirichlet.CoverCountProof
import YangMills.Construction.Dirichlet.GreenBoundsOnRegionsProof
import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
namespace YangMills.Construction.Dirichlet.NearCentres
section Lengths
variable {d : ℕ} {S : ℝ}
theorem norm_coe_le_abs_of_pos (hS : 0 < S) (x : ℝ) : ‖(x : AddCircle S)‖ ≤ |x| := by
  rw [AddCircle.norm_eq' S hS]
  have h := round_le (S⁻¹ * x) 0
  simp only [Int.cast_zero, sub_zero] at h
  calc S * |S⁻¹ * x - round (S⁻¹ * x)| ≤ S * |S⁻¹ * x| := by gcongr
    _ = |x| := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hS), ← mul_assoc, mul_inv_cancel₀ hS.ne', one_mul]
theorem exists_lift_abs_eq_norm (θ : AddCircle S) :
    ∃ x : ℝ, (x : AddCircle S) = θ ∧ |x| = ‖θ‖ := by apply _root_.YangMills.Construction.TorusMetric.exists_coe_eq_abs_eq_norm <;> assumption
theorem supNorm_torusProj_le_norm (v : Fin d → ℝ) : supNorm (torusProj d S v) ≤ ‖v‖ :=
  csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg _⟩ ⟨v, rfl, rfl⟩
theorem exists_lift_norm_eq_supNorm (hS : 0 < S) (p : PeriodicTorus d S) :
    ∃ v : Fin d → ℝ, torusProj d S v = p ∧ ‖v‖ = supNorm p := by
  choose v hv hn using fun μ => exists_lift_abs_eq_norm (p μ)
  have hproj : torusProj d S v = p := funext hv
  refine ⟨v, hproj, le_antisymm ?_ ?_⟩
  · refine le_csInf ⟨‖v‖, v, hproj, rfl⟩ ?_
    rintro _ ⟨w, hw, rfl⟩
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ => ?_
    rw [Real.norm_eq_abs, hn, ← congrFun hw μ]
    exact (norm_coe_le_abs_of_pos hS _).trans (by simpa using norm_le_pi_norm w μ)
  · rw [← hproj]
    exact supNorm_torusProj_le_norm v
theorem torusProj_add (v w : Fin d → ℝ) :
    torusProj d S (v + w) = torusProj d S v + torusProj d S w := by apply _root_.YangMills.Construction.Dirichlet.Commutator.torusProj_add <;> assumption
theorem supNorm_add_le (hS : 0 < S) (p q : PeriodicTorus d S) :
    supNorm (p + q) ≤ supNorm p + supNorm q := by
  obtain ⟨v, rfl, hv⟩ := exists_lift_norm_eq_supNorm hS p
  obtain ⟨w, rfl, hw⟩ := exists_lift_norm_eq_supNorm hS q
  rw [← torusProj_add, ← hv, ← hw]
  exact (supNorm_torusProj_le_norm _).trans (norm_add_le _ _)
theorem supNorm_neg (hS : 0 < S) (p : PeriodicTorus d S) : supNorm (-p) = supNorm p := by
  have key : ∀ p : PeriodicTorus d S, supNorm (-p) ≤ supNorm p := by
    intro p
    obtain ⟨v, rfl, hv⟩ := exists_lift_norm_eq_supNorm hS p
    have h : -torusProj d S v = torusProj d S (-v) := by
      funext μ
      simp [torusProj]
    rw [h, ← hv]
    simpa using supNorm_torusProj_le_norm (d := d) (S := S) (-v)
  refine le_antisymm (key p) ?_
  simpa using key (-p)
theorem supNorm_sub_comm (hS : 0 < S) (p q : PeriodicTorus d S) :
    supNorm (p - q) = supNorm (q - p) := by
  rw [← neg_sub, supNorm_neg hS]
theorem supNorm_sub_le_add (hS : 0 < S) (p q r : PeriodicTorus d S) :
    supNorm (p - r) ≤ supNorm (p - q) + supNorm (q - r) := by
  rw [← sub_add_sub_cancel p q r]
  exact supNorm_add_le hS _ _
end Lengths
variable {d L : ℕ} {S aMinus aPlus : ℝ}
theorem isNatAtLeastTwo_of_isPosEvenNat {r : ℝ} (h : IsPosEvenNat r) :
    IsNatAtLeastTwo r := by
  obtain ⟨k, hk, hr⟩ := h
  exact ⟨2 * k, by omega, by rw [hr]; push_cast; ring⟩
theorem mem_shellSites_centreIndex (𝒮 : BlockSetting d L aMinus aPlus S) {y : PeriodicTorus d S}
    (hy : y ∈ 𝒮.centres) : y ∈ shellSites L 𝒮.ξ 𝒮.Ω (𝒮.centreIndex y) := by apply _root_.YangMills.Construction.Dirichlet.RegionBounds.mem_shellSites_centreIndex <;> assumption
end YangMills.Construction.Dirichlet.NearCentres
