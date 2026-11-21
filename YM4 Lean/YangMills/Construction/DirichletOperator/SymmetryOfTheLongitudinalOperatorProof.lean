import YangMills.Construction.RegionSequence.AvgOpWeightSum
import YangMills.Construction.RegionSequence.BaseOperatorPositivityProof
import YangMills.Construction.RegionSequence.CellsAndAdjoints
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
open YangMills.Construction.RegionSequence.CellStructure (IsSelfAdjointOn)
noncomputable section
namespace YangMills.Construction.RegionSequence.LongOpSymmetryProof
theorem exists_mem_sub_orthogonal {W : Type} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hB : ∀ u, u ≠ 0 → 0 < B u u) (V : Submodule ℝ W) (v : W) :
    ∃ p ∈ V, ∀ w ∈ V, B (v - p) w = 0 := by
  let C : V →ₗ[ℝ] Module.Dual ℝ V := B.domRestrict₁₂ V V
  have hinj : Function.Injective C := by
    refine (injective_iff_map_eq_zero C).2 fun u hu => ?_
    by_contra hne
    have h₁ : B u u = 0 := LinearMap.congr_fun hu u
    have h₂ := hB u (by simpa using hne)
    exact h₂.ne' h₁
  have hsurj : Function.Surjective C :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).1 hinj
  obtain ⟨p, hp⟩ := hsurj ((B v).domRestrict V)
  refine ⟨p, p.2, fun w hw => ?_⟩
  have h : B p w = B v w := LinearMap.congr_fun hp ⟨w, hw⟩
  rw [map_sub, LinearMap.sub_apply, h, sub_self]
theorem finite_fineSite (R : NestedRegions) : Finite R.FineSite := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineSite <;> assumption
variable {R : NestedRegions}
theorem bondInner_comm (A B : R.FineBond → ℝ) : bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem innerSum_comm (f g : R.FineSite → ℝ) : innerSum f g = innerSum g f := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.innerSum_comm <;> assumption
section Finite
variable [Finite R.FineSite]
variable (R) in
def innerSumForm : (R.FineSite → ℝ) →ₗ[ℝ] (R.FineSite → ℝ) →ₗ[ℝ] ℝ :=
  let _ := Fintype.ofFinite R.FineSite
  LinearMap.mk₂ ℝ innerSum
    (fun a b c => by
      simp only [innerSum, finsum_eq_sum_of_fintype, Pi.add_apply, add_mul,
        Finset.sum_add_distrib, mul_add])
    (fun r a b => by
      simp only [innerSum, finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun a b c => by
      simp only [innerSum, finsum_eq_sum_of_fintype, Pi.add_apply, mul_add,
        Finset.sum_add_distrib])
    (fun r a b => by
      simp only [innerSum, finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
theorem innerSumForm_apply (f g : R.FineSite → ℝ) : innerSumForm R f g = innerSum f g := rfl
theorem innerSumForm_self_pos (f : R.FineSite → ℝ) (hf : f ≠ 0) : 0 < innerSumForm R f f := by
  let _ := Fintype.ofFinite R.FineSite
  rw [innerSumForm_apply]
  simp only [innerSum, finsum_eq_sum_of_fintype]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hf
  exact mul_pos (pow_pos R.ξ_pos 4) (Finset.sum_pos' (fun j _ => mul_self_nonneg _)
    ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩)
theorem blockAvg_add (f g : R.FineSite → ℝ) :
    blockAvg (f + g) = blockAvg f + blockAvg g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.blockAvg_add <;> assumption
theorem blockAvg_smul (r : ℝ) (f : R.FineSite → ℝ) :
    blockAvg (r • f) = r • blockAvg f := by apply _root_.YangMills.Construction.RegionSequence.Positivity.blockAvg_smul <;> assumption
variable (R) in
def avgKernelSubmodule : Submodule ℝ (R.FineSite → ℝ) where
  carrier := R.avgKernel
  add_mem' := fun ha hb => ⟨R.siteFns.add_mem ha.1 hb.1, by
    rw [blockAvg_add, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨R.siteFns.zero_mem, by
    simpa using blockAvg_smul (R := R) 0 0⟩
  smul_mem' := fun c _ ha => ⟨R.siteFns.smul_mem c ha.1, by
    rw [blockAvg_smul, ha.2, smul_zero]⟩
omit [Finite R.FineSite] in
theorem latticeLaplacian_add (f g : R.FineSite → ℝ) :
    latticeLaplacian (f + g) = latticeLaplacian f + latticeLaplacian g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.latticeLaplacian_add <;> assumption
omit [Finite R.FineSite] in
theorem latticeLaplacian_smul (r : ℝ) (f : R.FineSite → ℝ) :
    latticeLaplacian (r • f) = r • latticeLaplacian f := by apply _root_.YangMills.Construction.RegionSequence.Positivity.latticeLaplacian_smul <;> assumption
omit [Finite R.FineSite] in
theorem projSites_add (f g : R.FineSite → ℝ) :
    projSites (f + g) = projSites f + projSites g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.projSites_add <;> assumption
omit [Finite R.FineSite] in
theorem projSites_smul (r : ℝ) (f : R.FineSite → ℝ) :
    projSites (r • f) = r • projSites f := by apply _root_.YangMills.Construction.RegionSequence.Positivity.projSites_smul <;> assumption
variable (R) in
def dirichletLapLinear : (R.FineSite → ℝ) →ₗ[ℝ] (R.FineSite → ℝ) where
  toFun := dirichletLap
  map_add' f g := by
    simp only [dirichletLap, projSites_add, latticeLaplacian_add]
  map_smul' r f := by
    simp only [dirichletLap, projSites_smul, latticeLaplacian_smul, RingHom.id_apply]
variable (R) in
def lapImageKernel : Submodule ℝ (R.FineSite → ℝ) :=
  (avgKernelSubmodule R).map (dirichletLapLinear R)
theorem rangeProj_spec (f : R.FineSite → ℝ) :
    rangeProj f ∈ lapImageKernel R ∧
      ∀ w ∈ lapImageKernel R, innerSum (f - rangeProj f) w = 0 := by
  obtain ⟨p, hp, hp'⟩ :=
    exists_mem_sub_orthogonal (innerSumForm R) innerSumForm_self_pos (lapImageKernel R) f
  have e : (lapImageKernel R : Set (R.FineSite → ℝ)) =
      dirichletLap '' R.avgKernel := Submodule.map_coe _ _
  have h := Classical.epsilon_spec
    (p := fun p => p ∈ dirichletLap '' R.avgKernel ∧
      ∀ w ∈ dirichletLap '' R.avgKernel, innerSum (f - p) w = 0)
    ⟨p, e ▸ hp, fun w hw => hp' w (by rw [← SetLike.mem_coe, e]; exact hw)⟩
  exact ⟨by rw [← SetLike.mem_coe, e]; exact h.1,
    fun w hw => h.2 w (by rw [← SetLike.mem_coe, e] at hw; exact hw)⟩
end Finite
end YangMills.Construction.RegionSequence.LongOpSymmetryProof
