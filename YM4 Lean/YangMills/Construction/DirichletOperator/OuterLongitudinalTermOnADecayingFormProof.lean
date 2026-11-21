import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.ApproximateInverseAndLocalDefectsProof
import YangMills.Construction.DirichletOperator.OuterLongitudinalSourceAtTheCellsOfACubeProof
import YangMills.Construction.DirichletOperator.FormDecayingFromAPointOfACube
import YangMills.Construction.DirichletOperator.PropagatorBoundsForSourcesInFormsProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.RemainderEstimates YangMills.Construction.Weighted
noncomputable section
namespace YangMills.Construction.DirichletOperator.OuterLongitudinalBound
theorem cell_term_le {k ξ ξ' U e₁ x₁ E₁ x₂ E₂ n N : ℝ} (hk : 0 ≤ k) (hξ : 0 < ξ) (hξξ : ξ ≤ ξ')
    (hU : 0 ≤ U) (he₁ : 0 ≤ e₁) (hx₁ : x₁ ≤ e₁ * E₁) (hx₁0 : 0 ≤ x₁) (hx₂ : x₂ ≤ E₂) (hx₂0 : 0 ≤ x₂)
    (hE₁ : 0 ≤ E₁) (hn : n ≤ k * (ξ' ^ 2)⁻¹ * x₁) (hN : N ≤ ξ ^ 2 * U * x₂) (hN0 : 0 ≤ N) :
    n * N ≤ k * e₁ * U * (E₁ * E₂) := by
  have hξ' : 0 < ξ' := hξ.trans_le hξξ
  have hq : ξ ^ 2 * (ξ' ^ 2)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one (by positivity)).2 (pow_le_pow_left₀ hξ.le hξξ 2)
  have hW : 0 ≤ k * (ξ' ^ 2)⁻¹ * x₁ := by positivity
  calc n * N ≤ k * (ξ' ^ 2)⁻¹ * x₁ * (ξ ^ 2 * U * x₂) := mul_le_mul hn hN hN0 hW
    _ = (ξ ^ 2 * (ξ' ^ 2)⁻¹) * (k * U * x₁ * x₂) := by ring
    _ ≤ 1 * (k * U * x₁ * x₂) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ = k * U * x₁ * x₂ := one_mul _
    _ ≤ k * U * (e₁ * E₁) * E₂ := by
        have h₁ : k * U * x₁ ≤ k * U * (e₁ * E₁) := mul_le_mul_of_nonneg_left hx₁ (by positivity)
        exact mul_le_mul h₁ hx₂ hx₂0 (by positivity)
    _ = _ := by ring
theorem cast_L_pos (𝒯 : NestedRegions) : (0 : ℝ) < 𝒯.L := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.blockFactor_pos <;> assumption
theorem scaleSpacing_pos (𝒯 : NestedRegions) (n : ℤ) : 0 < Torus.scaleSpacing 𝒯.L 𝒯.ξ n := by apply _root_.YangMills.Construction.PartitionCubes.FirstTypeMaps.scaleSpacing_pos <;> assumption
theorem scale_le_scale_succ (𝒯 : NestedRegions) (n : ℕ) : 𝒯.scale n ≤ 𝒯.scale (n + 1) := by apply _root_.YangMills.Construction.CubeSourceProof.scale_le_scale_succ <;> assumption
theorem finite_fineBond (h : Torus.TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem weightedDist_nonneg (𝒯 : NestedRegions) (p q : 𝒯.Point) :
    0 ≤ 𝒯.weightedDist p q := by apply _root_.YangMills.Construction.DivSourceEstimate.weightedDist_nonneg <;> assumption
variable {𝒮 : NestedRegions} {M : ℕ}
theorem abs_le_supBond [Finite 𝒮.FineBond] (f : 𝒮.FineBond → ℝ) (b : 𝒮.FineBond) :
    |f b| ≤ supBond f :=
  le_ciSup (f := fun b => ‖f b‖) (finite_range _).bddAbove b
theorem subset_thickened (hl : Torus.TorusLengthsStatement) (Q : LevelCube 𝒮 M)
    (X : Set Q.system.setting.Point) : X ⊆ Q.thickened X := by
  intro x hx
  have h : supSetDist {x} X ≤ ENNReal.ofReal (supNorm (x - x)) :=
    le_trans (iInf₂_le x (Set.mem_singleton x)) (iInf₂_le x hx)
  rw [sub_self, (hl 4 _ Q.system.setting.side_pos).1.supNorm_zero] at h
  exact h.trans (by simp)
end YangMills.Construction.DirichletOperator.OuterLongitudinalBound
