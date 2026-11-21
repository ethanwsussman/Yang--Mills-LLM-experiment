import YangMills.Construction.Dirichlet.CommutatorBoundsProof
import YangMills.Construction.Dirichlet.FormsOperatorsProof
import YangMills.Construction.Dirichlet.HolderProductBound
import YangMills.Construction.DirichletOperator.BoundsAtOneCubeProof
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
noncomputable section
namespace YangMills.Construction.Dirichlet.HolderProduct
variable {d : ℕ} {S ξ : ℝ}
theorem exists_torusProj_eq (p : PeriodicTorus d S) : ∃ v : Fin d → ℝ, torusProj d S v = p := by apply _root_.YangMills.Construction.Dirichlet.Commutator.exists_torusProj_eq <;> assumption
theorem supNorm_le_norm_of_torusProj_eq {p : PeriodicTorus d S} {v : Fin d → ℝ}
    (h : torusProj d S v = p) : supNorm p ≤ ‖v‖ :=
  csInf_le ⟨0, by rintro _ ⟨w, _, rfl⟩; exact norm_nonneg w⟩ ⟨v, h, rfl⟩
theorem lOneNorm_le_sum_abs_of_torusProj_eq {p : PeriodicTorus d S} {v : Fin d → ℝ}
    (h : torusProj d S v = p) : lOneNorm p ≤ ∑ μ, |v μ| := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.lOneNorm_le_sum_abs_of_proj <;> assumption
theorem lOneNorm_nonneg' (p : PeriodicTorus d S) : 0 ≤ lOneNorm p := by
  apply Real.sInf_nonneg
  rintro _ ⟨w, _, rfl⟩
  exact Finset.sum_nonneg fun μ _ => abs_nonneg (w μ)
theorem finite_latticeSite {N : ℕ} (hN : 0 < N) (hS : S = N * ξ) : Finite (LatticeSite d S ξ) := by apply _root_.YangMills.Construction.Dirichlet.Forms.finite_latticeSite <;> assumption
theorem unitStep_ne_zero {N : ℕ} (hξ : 0 < ξ) (hN : 2 ≤ N) (hS : S = N * ξ) (μ : Fin d) :
    (unitStep d S ξ μ : PeriodicTorus d S) ≠ 0 := by
  intro h
  have h₁ : ((ξ : ℝ) : AddCircle S) = 0 := by
    have := congrFun h μ
    simpa [unitStep, torusProj] using this
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).1 h₁
  rw [zsmul_eq_mul, hS] at hn
  have h₂ : (n : ℝ) * N = 1 := by
    have : ((n : ℝ) * N - 1) * ξ = 0 := by linear_combination hn
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hξ.ne'
  have h₃ : n * (N : ℤ) = 1 := by exact_mod_cast h₂
  have h₄ : (N : ℤ) ∣ 1 := ⟨n, by linarith⟩
  have h₅ : (N : ℤ) ≤ 1 := Int.le_of_dvd one_pos h₄
  omega
theorem lOneNorm_unitStep_le (hξ : 0 < ξ) (μ : Fin d) :
    lOneNorm (unitStep d S ξ μ : PeriodicTorus d S) ≤ ξ := by
  have h : torusProj d S (Pi.single μ ξ) = (unitStep d S ξ μ : PeriodicTorus d S) := rfl
  refine (lOneNorm_le_sum_abs_of_torusProj_eq h).trans_eq ?_
  rw [Finset.sum_eq_single μ]
  · simp [abs_of_pos hξ]
  · intro ν _ hν
    simp [Pi.single_eq_of_ne hν]
  · simp
end YangMills.Construction.Dirichlet.HolderProduct
