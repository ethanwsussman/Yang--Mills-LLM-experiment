import YangMills.Construction.Dirichlet.NearCentresOfCubeProof
import YangMills.Construction.Torus.ProjSmallCubes
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.ProjCubes
variable {d : ℕ} {S : ℝ}
theorem norm_addCircle_le_abs (hS : 0 < S) (x : ℝ) : ‖(x : AddCircle S)‖ ≤ |x| := by apply _root_.YangMills.Construction.Dirichlet.NearCentres.norm_coe_le_abs_of_pos <;> assumption
theorem exists_coe_eq_abs_eq_norm (y : AddCircle S) :
    ∃ x : ℝ, (x : AddCircle S) = y ∧ |x| = ‖y‖ := by apply _root_.YangMills.Construction.TorusMetric.exists_coe_eq_abs_eq_norm <;> assumption
theorem torusProj_sub (v w : Fin d → ℝ) :
    torusProj d S v - torusProj d S w = torusProj d S (v - w) := by
  funext μ
  simp [torusProj]
theorem torusProj_add (v w : Fin d → ℝ) :
    torusProj d S v + torusProj d S w = torusProj d S (v + w) := by
  funext μ
  simp [torusProj]
theorem exists_minimal_lift (p : PeriodicTorus d S) :
    ∃ v : Fin d → ℝ, torusProj d S v = p ∧ ∀ μ, |v μ| = ‖p μ‖ := by
  choose v hv hv' using fun μ => exists_coe_eq_abs_eq_norm (p μ)
  exact ⟨v, funext hv, hv'⟩
theorem norm_torusProj_le (hS : 0 < S) (v : Fin d → ℝ) : ‖torusProj d S v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun μ => ?_
  exact (norm_addCircle_le_abs hS (v μ)).trans (norm_le_pi_norm v μ)
theorem supNorm_eq_norm (hS : 0 < S) (p : PeriodicTorus d S) : supNorm p = ‖p‖ := by
  obtain ⟨u, hu, hu'⟩ := exists_minimal_lift p
  have hb : BddBelow {r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = ‖v‖} :=
    ⟨0, by rintro r ⟨v, -, rfl⟩; exact norm_nonneg v⟩
  have hm : ‖u‖ ∈ {r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = ‖v‖} := ⟨u, hu, rfl⟩
  refine le_antisymm ((csInf_le hb hm).trans ?_) (le_csInf ⟨_, hm⟩ ?_)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg p)).2 fun μ => ?_
    rw [Real.norm_eq_abs, hu']
    exact norm_le_pi_norm p μ
  · rintro r ⟨v, rfl, rfl⟩
    exact norm_torusProj_le hS v
theorem lOneNorm_eq_sum_norm (hS : 0 < S) (p : PeriodicTorus d S) :
    lOneNorm p = ∑ μ, ‖p μ‖ := by
  obtain ⟨u, hu, hu'⟩ := exists_minimal_lift p
  have hb : BddBelow {r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = ∑ μ, |v μ|} :=
    ⟨0, by rintro r ⟨v, -, rfl⟩; exact Finset.sum_nonneg fun μ _ => abs_nonneg (v μ)⟩
  have hm : ∑ μ, |u μ| ∈ {r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = ∑ μ, |v μ|} :=
    ⟨u, hu, rfl⟩
  refine le_antisymm ((csInf_le hb hm).trans ?_) (le_csInf ⟨_, hm⟩ ?_)
  · exact (Finset.sum_congr rfl fun μ _ => hu' μ).le
  · rintro r ⟨v, rfl, rfl⟩
    exact Finset.sum_le_sum fun μ _ => norm_addCircle_le_abs hS (v μ)
theorem norm_torusProj_apply (hS : 0 < S) (u : Fin d → ℝ) (hu : ‖u‖ ≤ S / 2) (μ : Fin d) :
    ‖torusProj d S u μ‖ = |u μ| := by
  refine (AddCircle.norm_coe_eq_abs_iff S hS.ne').2 ?_
  rw [abs_of_pos hS]
  exact (norm_le_pi_norm u μ).trans hu
theorem injOn_torusProj_openCube (hS : 0 < S) (c : Fin d → ℝ) (s : ℝ) (hs : s ≤ S) :
    InjOn (torusProj d S) {v | ∀ μ, |v μ - c μ| < s / 2} := by
  intro v hv w hw hvw
  funext μ
  have h0 : ((v μ - w μ : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_sub, sub_eq_zero]
    exact congrFun hvw μ
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).1 h0
  have hlt : |v μ - w μ| < S := by
    have h1 := abs_sub_le (v μ) (c μ) (w μ)
    have h2 := hv μ
    have h3 := hw μ
    rw [abs_sub_comm (c μ) (w μ)] at h1
    linarith
  have hn' : (n : ℝ) * S = v μ - w μ := by simpa using hn
  rw [← hn', abs_mul, abs_of_pos hS] at hlt
  have h1 : |(n : ℝ)| < 1 := by
    by_contra hcon
    exact absurd hlt (not_lt.2 (le_mul_of_one_le_left hS.le (not_lt.1 hcon)))
  have h2 : |n| < 1 := by exact_mod_cast h1
  have h3 : n = 0 := Int.abs_lt_one_iff.1 h2
  rw [h3] at hn'
  have h4 : v μ - w μ = 0 := by simpa using hn'.symm
  linarith
theorem projFacts_hold : ProjFactsHold := by
  intro d S hS
  refine ⟨fun c s hs => injOn_torusProj_openCube hS c s hs, ?_, ?_, ?_, ?_, ?_⟩
  · intro v w h
    rw [torusProj_sub, supNorm_eq_norm hS]
    refine le_antisymm (norm_torusProj_le hS _) ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ => ?_
    rw [Real.norm_eq_abs, ← norm_torusProj_apply hS (v - w) h μ]
    exact norm_le_pi_norm (torusProj d S (v - w)) μ
  · intro v w h
    rw [torusProj_sub, lOneNorm_eq_sum_norm hS]
    exact Finset.sum_congr rfl fun μ _ => norm_torusProj_apply hS (v - w) h μ
  · intro v
    rw [lOneNorm_eq_sum_norm hS]
    exact Finset.sum_le_sum fun μ _ => norm_addCircle_le_abs hS (v μ)
  · intro p q
    simp only [lOneNorm_eq_sum_norm hS, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun μ _ => norm_add_le (p μ) (q μ)
  · intro c σ p hσ
    simp only [cubeAt, mem_ofPred_eq, supNorm_eq_norm hS]
    constructor
    · intro h
      obtain ⟨u, hu, hu'⟩ := exists_minimal_lift (p - torusProj d S c)
      refine ⟨u + c, ?_, fun μ => ?_⟩
      · rw [← torusProj_add, hu, sub_add_cancel]
      · rw [Pi.add_apply, add_sub_cancel_right, hu']
        exact (norm_le_pi_norm _ μ).trans h
    · rintro ⟨v, rfl, hv⟩
      rw [torusProj_sub]
      refine (norm_torusProj_le hS _).trans ?_
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => ?_
      simpa using hv μ
end YangMills.Construction.ProjCubes
end
