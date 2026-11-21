import YangMills.Construction.RegionSequence.AvgOpWeightSum
import YangMills.Construction.RegionSequence.BaseOperatorPositivityProof
import YangMills.Construction.RegionSequence.BlockAverageLift
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus
namespace RegionSequence.GaugeLapPositivityProof
open NestedRegions
theorem scaleSpacing_pos (𝒮 : NestedRegions) (n : ℕ) : 0 < scaleSpacing 𝒮.L 𝒮.ξ n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
section InnerProduct
variable {𝒮 : NestedRegions}
variable [Fintype 𝒮.FineSite]
theorem innerSum_eq_finset_sum (f g : 𝒮.FineSite → ℝ) :
    innerSum f g = 𝒮.ξ ^ 4 * ∑ x, f x * g x := by
  rw [innerSum, finsum_eq_sum_of_fintype]
end InnerProduct
section DirichletPart
variable {𝒮 : NestedRegions}
theorem projSites_eq_self_of_mem {f : 𝒮.FineSite → ℝ} (hf : f ∈ 𝒮.siteFns) :
    projSites f = f := by
  funext x
  by_cases hx : (x : 𝒮.Point) ∈ 𝒮.Ω 0
  · simp [projSites, restrictTo, hx]
  · simp [projSites, restrictTo, hx, show f x = 0 from hf x hx]
theorem projSites_mem_siteFns (f : 𝒮.FineSite → ℝ) : projSites f ∈ 𝒮.siteFns := by
  intro x hx
  simp [projSites, restrictTo, hx]
theorem innerSum_projSites_left {f : 𝒮.FineSite → ℝ} (hf : f ∈ 𝒮.siteFns)
    (g : 𝒮.FineSite → ℝ) : innerSum (projSites g) f = innerSum g f := by
  simp only [innerSum]
  congr 1
  refine finsum_congr fun x => ?_
  by_cases hx : (x : 𝒮.Point) ∈ 𝒮.Ω 0
  · simp [projSites, restrictTo, hx]
  · simp [show f x = 0 from hf x hx]
end DirichletPart
section AveragePart
variable {𝒮 : NestedRegions}
variable [Fintype 𝒮.FineSite]
theorem blockAvg_eq_finset_sum (f : 𝒮.FineSite → ℝ) (y : 𝒮.allCentres) :
    blockAvg f y = ((𝒮.L : ℝ) ^ (𝒮.level y * 4))⁻¹ *
      ∑ x, (𝒮.fineBlock (𝒮.level y) y).indicator f x := by
  rw [blockAvg, finsum_mem_def, finsum_eq_sum_of_fintype]
theorem blockAvg_add_fn (f g : 𝒮.FineSite → ℝ) :
    blockAvg (f + g) = blockAvg f + blockAvg g := by
  funext y
  simp only [blockAvg_eq_finset_sum, Pi.add_apply, indicator_add', Finset.sum_add_distrib, mul_add]
theorem blockAvg_smul_fn (c : ℝ) (f : 𝒮.FineSite → ℝ) :
    blockAvg (c • f) = c • blockAvg f := by
  funext y
  have h : ∀ (B : Set 𝒮.FineSite) (x : 𝒮.FineSite), B.indicator (c • f) x = c * B.indicator f x := by
    intro B x
    by_cases hx : x ∈ B <;> simp [hx]
  simp only [blockAvg_eq_finset_sum, Pi.smul_apply, h, smul_eq_mul, ← Finset.mul_sum]
  ring
variable [Fintype 𝒮.allCentres]
theorem coarseInner_eq_finset_sum (ω ω' : 𝒮.Coarse) :
    coarseInner ω ω' = ∑ y : 𝒮.allCentres, 𝒮.levelScale y ^ 4 * ω y * ω' y := by
  rw [coarseInner, finsum_eq_sum_of_fintype]
def pairAgainstAvg (ω : 𝒮.Coarse) : (𝒮.FineSite → ℝ) →ₗ[ℝ] ℝ where
  toFun u := coarseInner ω (blockAvg u)
  map_add' f g := by
    simp only [coarseInner_eq_finset_sum, blockAvg_add_fn, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [coarseInner_eq_finset_sum, blockAvg_smul_fn, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
theorem exists_blockAvg_adjoint (ω : 𝒮.Coarse) :
    ∃ v : 𝒮.FineSite → ℝ, v ∈ 𝒮.siteFns ∧
      ∀ u ∈ 𝒮.siteFns, innerSum v u = coarseInner ω (blockAvg u) := by
  classical
  set F := pairAgainstAvg ω with hF
  refine ⟨projSites fun x => (𝒮.ξ ^ 4)⁻¹ * F (fun j => if x = j then 1 else 0),
    projSites_mem_siteFns _, fun u hu => ?_⟩
  have hFu : coarseInner ω (blockAvg u) = F u := rfl
  rw [innerSum_projSites_left hu, innerSum_eq_finset_sum, hFu, LinearMap.pi_apply_eq_sum_univ F u,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hξ : 𝒮.ξ ^ 4 ≠ 0 := (pow_pos 𝒮.ξ_pos 4).ne'
  rw [smul_eq_mul]
  beta_reduce
  linear_combination ((F fun j => if x = j then 1 else 0) * u x) * mul_inv_cancel₀ hξ
theorem blockAvgAdj_spec (ω : 𝒮.Coarse) :
    blockAvgAdj ω ∈ 𝒮.siteFns ∧
      ∀ u ∈ 𝒮.siteFns, innerSum (blockAvgAdj ω) u = coarseInner ω (blockAvg u) :=
  Classical.epsilon_spec (p := fun v => v ∈ (𝒮.siteFns : Set (𝒮.FineSite → ℝ)) ∧
    ∀ u ∈ (𝒮.siteFns : Set (𝒮.FineSite → ℝ)), innerSum v u = coarseInner ω (blockAvg u))
    (exists_blockAvg_adjoint ω)
end AveragePart
section FormPart
variable {𝒮 : NestedRegions}
theorem exists_eq_sum_zsmul_unitStep (x : 𝒮.FineSite) :
    ∃ k : Fin 4 → ℤ, x = ∑ μ, k μ • unitStep 4 𝒮.side 𝒮.ξ μ := by
  obtain ⟨k, hk⟩ := x.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [hk]
  funext ν
  simp only [AddSubgroup.val_finset_sum, AddSubgroupClass.coe_zsmul, Finset.sum_apply,
    Pi.smul_apply, unitStep, torusProj]
  rw [Finset.sum_eq_single ν]
  · simp only [Pi.single_eq_same]
    rw [← zsmul_eq_mul]
    exact map_zsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples 𝒮.side)) (k ν) 𝒮.ξ
  · intro μ _ hne
    simp [Pi.single_eq_of_ne (Ne.symm hne)]
  · simp
variable [Fintype 𝒮.FineSite] [Fintype 𝒮.allCentres]
end FormPart
end RegionSequence.GaugeLapPositivityProof
end YangMills.Construction
