import YangMills.Construction.DirichletOperator.BondsNearACubeCarriedToItsTorusProof
import YangMills.Construction.DirichletOperator.BoundsOnTheCoefficientsOfACubeProof
import YangMills.Construction.DirichletOperator.CubeTransfersAreAdjointProof
import YangMills.Construction.DirichletOperator.DecayOfAFormFromBoundsOnSmallCubes
import YangMills.Construction.DirichletOperator.DifferenceOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.DirichletOperator.FactsOfTheCellsOfACube
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
open CubeTorus (tensorModulusAt)
namespace DirichletOperator.SmallCubeDecay
theorem exists_lift_norm_lt (hT : TorusLengthsStatement) {S : ℝ} (hS : 0 < S) (p : PeriodicTorus 4 S)
    {r : ℝ} (h : supNorm p < r) : ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ ‖v‖ < r := by
  obtain ⟨v, hv⟩ := (hT 4 S hS).1.torusProj_surjective p
  unfold supNorm at h
  have hne : ({r | ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ r = ‖v‖} : Set ℝ).Nonempty :=
    ⟨‖v‖, v, hv, rfl⟩
  obtain ⟨t, ⟨v', hv', rfl⟩, ht⟩ := exists_lt_of_csInf_lt hne h
  exact ⟨v', hv', ht⟩
theorem supNorm_torusProj_le {S : ℝ} (v : Fin 4 → ℝ) : supNorm (torusProj 4 S v) ≤ ‖v‖ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_proj_le <;> assumption
theorem proj_add {S : ℝ} (v v' : Fin 4 → ℝ) :
    torusProj 4 S (v + v') = torusProj 4 S v + torusProj 4 S v' := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_add <;> assumption
theorem proj_neg {S : ℝ} (v : Fin 4 → ℝ) : torusProj 4 S (-v) = -torusProj 4 S v := by apply _root_.YangMills.Construction.PartitionCubes.TorusTransfer.torusProj_neg <;> assumption
theorem proj_sub {S : ℝ} (v v' : Fin 4 → ℝ) :
    torusProj 4 S (v - v') = torusProj 4 S v - torusProj 4 S v' := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusBonds.torusProj_sub <;> assumption
def shift (ρ : ℝ) (e : Fin 4 → Fin 3) : Fin 4 → ℝ := fun μ => 2 * ρ * (((e μ : ℕ) : ℝ) - 1)
variable {R : NestedRegions} {M : ℕ}
theorem level_scale_pos (R : NestedRegions) (n : ℕ) : 0 < R.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem weighted_sum_le {a c N₀ N₁ C A₀ A₁ E : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (h₀ : N₀ ≤ C * A₀ * E)
    (h₁ : N₁ ≤ C * A₁ * E) : a * N₀ + c * N₁ ≤ C * (a * A₀ + c * A₁) * E :=
  calc a * N₀ + c * N₁ ≤ a * (C * A₀ * E) + c * (C * A₁ * E) :=
        add_le_add (mul_le_mul_of_nonneg_left h₀ ha) (mul_le_mul_of_nonneg_left h₁ hc)
    _ = C * (a * A₀ + c * A₁) * E := by ring
end DirichletOperator.SmallCubeDecay
end YangMills.Construction
