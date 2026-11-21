import YangMills.Construction.DirichletOperator.DistanceToTheComplementAndTheCuts
import YangMills.Construction.DirichletOperator.WhereThePartitionFunctionOfACubeLives
import YangMills.Construction.PartitionCubes.DiffBoundsFromDerivsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.PartitionCubes.PartitionFnSupport
theorem exists_torusProj_eq {S : ℝ} (p : PeriodicTorus 4 S) :
    ∃ v : Fin 4 → ℝ, torusProj 4 S v = p := by apply _root_.YangMills.Construction.PartitionCubes.FiniteDifference.exists_torusProj_eq <;> assumption
theorem bddBelow_liftNorms {S : ℝ} (p : PeriodicTorus 4 S) :
    BddBelow {r | ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ r = ‖v‖} :=
  ⟨0, by rintro r ⟨v, -, rfl⟩; exact norm_nonneg v⟩
theorem torusSupNorm_add_le {S : ℝ} (p q : PeriodicTorus 4 S) :
    supNorm (p + q) ≤ supNorm p + supNorm q := by
  obtain ⟨v₀, hv₀⟩ := exists_torusProj_eq p
  obtain ⟨w₀, hw₀⟩ := exists_torusProj_eq q
  have key : ∀ v w : Fin 4 → ℝ, torusProj 4 S v = p → torusProj 4 S w = q →
      supNorm (p + q) ≤ ‖v‖ + ‖w‖ := by
    intro v w hv hw
    refine (csInf_le (bddBelow_liftNorms _) ⟨v + w, ?_, rfl⟩).trans (norm_add_le v w)
    subst hv hw
    funext μ
    simp [torusProj]
  have h₁ : ∀ w : Fin 4 → ℝ, torusProj 4 S w = q → supNorm (p + q) - ‖w‖ ≤ supNorm p := by
    intro w hw
    refine le_csInf ⟨‖v₀‖, v₀, hv₀, rfl⟩ ?_
    rintro r ⟨v, hv, rfl⟩
    linarith [key v w hv hw]
  have h₂ : supNorm (p + q) - supNorm p ≤ supNorm q := by
    refine le_csInf ⟨‖w₀‖, w₀, hw₀, rfl⟩ ?_
    rintro r ⟨w, hw, rfl⟩
    linarith [h₁ w hw]
  linarith
end YangMills.Construction.PartitionCubes.PartitionFnSupport
