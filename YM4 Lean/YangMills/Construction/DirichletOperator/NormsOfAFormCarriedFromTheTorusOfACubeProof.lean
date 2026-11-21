import YangMills.Construction.DirichletOperator.ComparisonEstimatesOnTheCubeProof
import YangMills.Construction.DirichletOperator.ComparisonEstimatesOnTheTorusProof
import YangMills.Construction.DirichletOperator.FactsOfTheCellsOfACube
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.CubeTorus (levelSpacing)
noncomputable section
namespace YangMills.Construction.DirichletOperator.TransferredFormNorms.Argument
theorem finite_fineBond (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineBond <;> assumption
section Norms
variable {𝒯 : NestedRegions}
theorem sum_sq_le_sq_sum_of_nonneg {ι : Type} (s : Finset ι) (a : ι → ℝ) (h : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, a i ^ 2 ≤ (∑ i ∈ s, a i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have h₀ := h i (Finset.mem_insert_self _ _)
    have h₁ : ∀ j ∈ s, 0 ≤ a j := fun j hj => h j (Finset.mem_insert_of_mem hj)
    have h₂ := ih h₁
    have h₃ : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg h₁
    nlinarith [mul_nonneg h₀ h₃]
theorem abs_le_supSite (f : 𝒯.FineSite → ℝ) (x : 𝒯.FineSite) : |f x| ≤ supSite f := by apply _root_.YangMills.Construction.DivSourceEstimate.abs_le_supSite <;> assumption
theorem supSite_nonneg (f : 𝒯.FineSite → ℝ) : 0 ≤ supSite f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
end Norms
section EvaluationMaps
variable {𝒮 : NestedRegions}
variable (𝔏 : CubeSystem 𝒮) (X : Set 𝒮.Point)
theorem mem_of_indicator_ne_zero {x : 𝒮.Point} (h : indicator X (fun _ => (1 : ℝ)) x ≠ 0) :
    x ∈ X := by
  by_contra hx
  exact h (indicator_of_notMem hx _)
end EvaluationMaps
section Transfer
variable {𝒮 : NestedRegions} {M : ℕ}
theorem mapSite_secondType (Q : LevelCube 𝒮 M) (x : 𝒮.FineSite) :
    Q.secondTypeSystem.mapSite x = x := by
  apply Subtype.ext
  exact Classical.epsilon_spec (p := fun y : 𝒮.FineSite => (y : 𝒮.Point) = (x : 𝒮.Point))
    ⟨x, rfl⟩
theorem mapBond_secondType (Q : LevelCube 𝒮 M) (b : 𝒮.FineBond) :
    Q.secondTypeSystem.mapBond b = b := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.mapBond_secondType <;> assumption
end Transfer
section Rules
variable {𝒮 : NestedRegions} {𝔏 : CubeSystem 𝒮}
structure PullsThrough (𝔏 : CubeSystem 𝒮) (ζ : 𝒮.FineSite → ℝ)
    (rd : (𝒮.FineSite → ℝ) → 𝔏.setting.FineSite → ℝ) : Prop where
  ξ_eq : 𝔏.setting.ξ = 𝒮.ξ
  bondL2_le : ∀ (φ : 𝒮.FineSite → ℝ) (w : 𝔏.setting.FineBond → ℝ),
    bondL2 (fun b => (ζ * φ) b.source * w (𝔏.mapBond b)) ≤ bondL2 (smulSiteBond (rd (ζ * φ)) w)
  mapBond_shiftUp : ∀ (ν : Fin 4) (b : 𝒮.FineBond), ζ b.source ≠ 0 →
    𝔏.mapBond (shiftUp ν b) = shiftUp ν (𝔏.mapBond b)
  mapBond_shiftUp_two : ∀ (ν ρ : Fin 4) (b : 𝒮.FineBond), ζ b.source ≠ 0 →
    𝔏.mapBond (shiftUp ρ (shiftUp ν b)) = shiftUp ρ (shiftUp ν (𝔏.mapBond b))
variable {ζ : 𝒮.FineSite → ℝ} {rd : (𝒮.FineSite → ℝ) → 𝔏.setting.FineSite → ℝ}
theorem PullsThrough.value_le (C : PullsThrough 𝔏 ζ rd) (h : 𝒮.FineSite → ℝ)
    (v : 𝔏.setting.FineBond → ℝ) :
    bondL2 (smulSiteBond ζ fun b => h b.source * v (𝔏.mapBond b)) ≤
      bondL2 (smulSiteBond (rd (ζ * h)) v) := by
  refine le_of_eq_of_le (congrArg bondL2 ?_) (C.bondL2_le h v)
  funext b
  show ζ b.source • (h b.source * v (𝔏.mapBond b)) = (ζ b.source * h b.source) * v (𝔏.mapBond b)
  rw [smul_eq_mul, mul_assoc]
end Rules
section Geometry
theorem supNorm_add_le {S : ℝ} (hc : Function.Surjective (torusProj 4 S)) (p q : PeriodicTorus 4 S) :
    supNorm (p + q) ≤ supNorm p + supNorm q := by apply _root_.YangMills.Construction.TorusComparisonProof.supNorm_add_le <;> assumption
variable {𝒮 : NestedRegions} {M : ℕ}
theorem supNorm_unitStep_le (μ : Fin 4) :
    supNorm ((unitStep 4 𝒮.side 𝒮.ξ μ : 𝒮.FineSite) : 𝒮.Point) ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.CubeTorusComparison.Estimates.supNorm_unitStep_le <;> assumption
end Geometry
section Main
variable {𝒮 : NestedRegions} {M : ℕ}
end Main
end YangMills.Construction.DirichletOperator.TransferredFormNorms.Argument
