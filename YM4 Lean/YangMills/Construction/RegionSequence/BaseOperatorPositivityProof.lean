import YangMills.Construction.RegionSequence.AvgOpWeightFormula
import YangMills.Construction.RegionSequence.GradientAdjointsOnTorus
import YangMills.Construction.SeparatedSequences.ClassExpansionsInASettingOfRegionsProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.RegionSequence.Positivity
section Finite
variable {X : Type}
theorem finsum_add_mul [Finite X] (f g h : X → ℝ) :
    ∑ᶠ x, (f + g) x * h x = ∑ᶠ x, f x * h x + ∑ᶠ x, g x * h x := by
  rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finsum_congr fun x => by simp [add_mul]
theorem exists_orthogonal_proj [Finite X] (K : Submodule ℝ (X → ℝ)) (f : X → ℝ) :
    ∃ r ∈ K, ∀ w ∈ K, ∑ᶠ x, (f - r) x * w x = 0 := by
  classical
  have := Fintype.ofFinite X
  let e : (X → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ X := (WithLp.linearEquiv 2 ℝ (X → ℝ)).symm
  let K' : Submodule ℝ (EuclideanSpace ℝ X) := K.map (e : (X → ℝ) →ₗ[ℝ] EuclideanSpace ℝ X)
  obtain ⟨y, hy, z, hz, hyz⟩ := K'.exists_add_mem_mem_orthogonal (e f)
  obtain ⟨r, hr, rfl⟩ := hy
  refine ⟨r, hr, fun w hw => ?_⟩
  have hz' := (Submodule.mem_orthogonal' K' z).1 hz (e w) ⟨w, hw, rfl⟩
  have hfr : ∀ x, (f - r) x = z x := by
    intro x
    have := congrArg (fun t : EuclideanSpace ℝ X => t x) hyz
    simp [e] at this
    simp [this]
  rw [finsum_eq_sum_of_fintype]
  simp only [hfr]
  simpa [PiLp.inner_apply, e, mul_comm] using hz'
end Finite
variable {𝒮 : NestedRegions}
theorem finite_fineSite (hL : TorusLengthsStatement) (𝒮 : NestedRegions) : Finite 𝒮.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
theorem finite_fineBond (hL : TorusLengthsStatement) (𝒮 : NestedRegions) : Finite 𝒮.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem bondInner_comm (A A' : 𝒮.FineBond → ℝ) : bondInner A A' = bondInner A' A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem innerSum_comm (f g : 𝒮.FineSite → ℝ) : innerSum f g = innerSum g f := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.innerSum_comm <;> assumption
theorem bondInner_add_left [Finite 𝒮.FineBond] (A B C : 𝒮.FineBond → ℝ) :
    bondInner (A + B) C = bondInner A C + bondInner B C := by
  simp only [bondInner, finsum_add_mul, mul_add]
theorem projSites_add (f g : 𝒮.FineSite → ℝ) :
    projSites (f + g) = projSites f + projSites g := by
  funext x
  by_cases hx : (x : 𝒮.Point) ∈ 𝒮.Ω 0 <;> simp [projSites, restrictTo, hx]
theorem projSites_smul (c : ℝ) (f : 𝒮.FineSite → ℝ) :
    projSites (c • f) = c • projSites f := by
  funext x
  by_cases hx : (x : 𝒮.Point) ∈ 𝒮.Ω 0 <;> simp [projSites, restrictTo, hx]
theorem latticeLaplacian_add (f g : 𝒮.FineSite → ℝ) :
    latticeLaplacian (f + g) = latticeLaplacian f + latticeLaplacian g := by
  funext x
  simp only [latticeLaplacian, latticeDiv, Dirichlet.grad, backwardDiff, forwardDiff,
    Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun μ _ => by ring
theorem latticeLaplacian_smul (c : ℝ) (f : 𝒮.FineSite → ℝ) :
    latticeLaplacian (c • f) = c • latticeLaplacian f := by
  funext x
  simp only [latticeLaplacian, latticeDiv, Dirichlet.grad, backwardDiff, forwardDiff,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => by ring
def dirichletLapLinear (𝒮 : NestedRegions) : (𝒮.FineSite → ℝ) →ₗ[ℝ] (𝒮.FineSite → ℝ) where
  toFun := dirichletLap
  map_add' f g := by
    simp only [dirichletLap, projSites_add, latticeLaplacian_add]
  map_smul' c f := by
    simp only [dirichletLap, projSites_smul, latticeLaplacian_smul, RingHom.id_apply]
theorem blockAvg_add [Finite 𝒮.FineSite] (f g : 𝒮.FineSite → ℝ) :
    blockAvg (f + g) = blockAvg f + blockAvg g := by
  funext y
  simp only [blockAvg, Pi.add_apply]
  rw [finsum_mem_add_distrib (Set.toFinite _), mul_add]
theorem blockAvg_smul [Finite 𝒮.FineSite] (c : ℝ) (f : 𝒮.FineSite → ℝ) :
    blockAvg (c • f) = c • blockAvg f := by
  funext y
  simp only [blockAvg, Pi.smul_apply, smul_eq_mul]
  rw [← mul_finsum_mem]
  ring
def avgKernelSubmodule (𝒮 : NestedRegions) [Finite 𝒮.FineSite] :
    Submodule ℝ (𝒮.FineSite → ℝ) where
  carrier := 𝒮.avgKernel
  add_mem' := fun {f g} hf hg => ⟨𝒮.siteFns.add_mem hf.1 hg.1, by
    rw [blockAvg_add, hf.2, hg.2, add_zero]⟩
  zero_mem' := ⟨𝒮.siteFns.zero_mem, by
    funext y
    simp [blockAvg]⟩
  smul_mem' := fun c f hf => ⟨𝒮.siteFns.smul_mem c hf.1, by
    rw [blockAvg_smul, hf.2, smul_zero]⟩
theorem rangeProj_spec [Finite 𝒮.FineSite] (f : 𝒮.FineSite → ℝ) :
    rangeProj f ∈ dirichletLap '' 𝒮.avgKernel ∧
      ∀ w ∈ dirichletLap '' 𝒮.avgKernel, innerSum (f - rangeProj f) w = 0 := by
  obtain ⟨r, hr, hw⟩ := exists_orthogonal_proj ((avgKernelSubmodule 𝒮).map (dirichletLapLinear 𝒮)) f
  exact Classical.epsilon_spec
    (p := fun r => r ∈ dirichletLap '' 𝒮.avgKernel ∧
      ∀ w ∈ dirichletLap '' 𝒮.avgKernel, innerSum (f - r) w = 0)
    ⟨r, hr, fun w hw' => by
      rw [innerSum, hw w hw', mul_zero]⟩
end YangMills.Construction.RegionSequence.Positivity
