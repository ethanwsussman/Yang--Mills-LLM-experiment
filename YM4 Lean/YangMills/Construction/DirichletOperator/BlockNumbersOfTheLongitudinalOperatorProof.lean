import YangMills.Construction.DirichletOperator.BlockNormCalculus
import YangMills.Construction.DirichletOperator.TermsOfTheRemainder
import YangMills.Construction.RegionSequence.CellsAndAdjoints
import YangMills.Construction.DirichletOperator.BoundsOnTheOperatorsOfASeparatedSequenceProof
import YangMills.Construction.DirichletOperator.WeightedDistanceOutOfACubeProof
import YangMills.Construction.RegionSequence.GaugeProjectionsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions
open RegionSequence.CellStructure (IsSelfAdjointOn)
open RemainderEstimates (FormEndo ActsAs)
namespace LongOpBlocks
structure IsPosPairing {W : Type} [AddCommGroup W] [Module ℝ W] (p : W → W → ℝ) : Prop where
  comm : ∀ a b, p a b = p b a
  add : ∀ a b c, p (a + b) c = p a c + p b c
  smul : ∀ (r : ℝ) a b, p (r • a) b = r * p a b
  pos : ∀ a, a ≠ 0 → 0 < p a a
namespace IsPosPairing
variable {W : Type} [AddCommGroup W] [Module ℝ W] {p : W → W → ℝ}
theorem add_right (h : IsPosPairing p) (a b c : W) : p a (b + c) = p a b + p a c := by
  rw [h.comm, h.add, h.comm b, h.comm c]
theorem smul_right (h : IsPosPairing p) (r : ℝ) (a b : W) : p a (r • b) = r * p a b := by
  rw [h.comm, h.smul, h.comm b]
theorem sub_left (h : IsPosPairing p) (a b c : W) : p (a - b) c = p a c - p b c := by
  have := h.add (a - b) b c
  rw [sub_add_cancel] at this
  linarith
theorem sub_right (h : IsPosPairing p) (a b c : W) : p a (b - c) = p a b - p a c := by
  rw [h.comm, h.sub_left, h.comm b, h.comm c]
theorem eq_zero_of_self_eq_zero (h : IsPosPairing p) {a : W} (ha : p a a = 0) : a = 0 := by
  by_contra hne
  exact (h.pos a hne).ne' ha
theorem eq_of_forall_mem (h : IsPosPairing p) {X : Submodule ℝ W} {a b : W} (ha : a ∈ X)
    (hb : b ∈ X) (hab : ∀ u ∈ X, p a u = p b u) : a = b := by
  apply sub_eq_zero.1
  apply h.eq_zero_of_self_eq_zero
  rw [h.sub_left, hab _ (X.sub_mem ha hb), sub_self]
theorem restrict (h : IsPosPairing p) (X : Submodule ℝ W) :
    IsPosPairing (fun a b : X => p a b) where
  comm a b := h.comm _ _
  add a b c := h.add _ _ _
  smul r a b := h.smul _ _ _
  pos a ha := h.pos _ (by simpa using ha)
theorem exists_repr [FiniteDimensional ℝ W] (h : IsPosPairing p) (l : W →ₗ[ℝ] ℝ) :
    ∃ v, ∀ u, p v u = l u := by
  let B : W →ₗ[ℝ] Module.Dual ℝ W := LinearMap.mk₂ ℝ p h.add
    (fun r a b => by rw [h.smul, smul_eq_mul]) h.add_right
    (fun r a b => by rw [h.smul_right, smul_eq_mul])
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun a ha => h.eq_zero_of_self_eq_zero ?_
    exact LinearMap.congr_fun ha a
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := W)).symm).1 hinj
  obtain ⟨v, hv⟩ := hsurj l
  exact ⟨v, fun u => LinearMap.congr_fun hv u⟩
theorem orthProjValue_spec [Nonempty W] [FiniteDimensional ℝ W] (h : IsPosPairing p)
    (Y : Submodule ℝ W) (f : W) :
    orthProjValue (Y : Set W) p f ∈ Y ∧
      ∀ w ∈ Y, p (f - orthProjValue (Y : Set W) p f) w = 0 := by
  let l : Y →ₗ[ℝ] ℝ :=
    { toFun := fun u => p f u
      map_add' := fun a b => h.add_right _ _ _
      map_smul' := fun r a => by
        rw [RingHom.id_apply, smul_eq_mul]
        exact h.smul_right _ _ _ }
  obtain ⟨v, hv⟩ := (h.restrict Y).exists_repr l
  exact Classical.epsilon_spec (p := fun r => r ∈ (Y : Set W) ∧ ∀ w ∈ (Y : Set W), p (f - r) w = 0)
    ⟨v, v.2, fun w hw => by
      rw [h.sub_left]
      have := hv ⟨w, hw⟩
      change p v w = p f w at this
      rw [this, sub_self]⟩
end IsPosPairing
theorem isPosPairing_weightedSum {ι : Type} [Finite ι] {c : ℝ} (hc : 0 < c) :
    IsPosPairing (fun a b : ι → ℝ => c * ∑ᶠ i, a i * b i) := by
  let _ := Fintype.ofFinite ι
  refine ⟨fun a b => ?_, fun a b d => ?_, fun r a b => ?_, fun a ha => ?_⟩
  · simp only [finsum_eq_sum_of_fintype, mul_comm (a _)]
  · simp only [finsum_eq_sum_of_fintype, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  · simp only [finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [finsum_eq_sum_of_fintype]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    refine mul_pos hc (Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩)
    exact mul_self_pos.2 hi
theorem spacingLattice_finite {σ S : ℝ} (K : ℤ) (hK : K ≠ 0) (hS : S = K * σ) :
    (spacingLattice 4 S σ : Set (PeriodicTorus 4 S)).Finite := by apply _root_.YangMills.Construction.RegionSequence.GaugeProjections.spacingLattice_finite <;> assumption
variable (𝒮 : NestedRegions)
theorem levelScale_pos (y : 𝒮.Point) : 0 < 𝒮.levelScale y := by apply _root_.YangMills.Construction.RegionSequence.OperatorEstimates.levelScale_pos <;> assumption
instance instFiniteFineSite : Finite 𝒮.FineSite := by
  obtain ⟨k, hk⟩ := 𝒮.side_mem_zmultiples
  have hs : scaleSpacing 𝒮.L 𝒮.ξ 𝒮.s = (𝒮.L : ℝ) ^ 𝒮.s * 𝒮.ξ := by
    simp [scaleSpacing]
  rw [hs] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    have := 𝒮.side_pos
    simp [hk] at this
  have hne : k * 2 * (𝒮.L : ℤ) ^ 𝒮.s ≠ 0 := by
    have : (𝒮.L : ℤ) ≠ 0 := by
      have := 𝒮.thirteen_le_L
      omega
    positivity
  refine (spacingLattice_finite (k * 2 * (𝒮.L : ℤ) ^ 𝒮.s) hne ?_).to_subtype
  rw [hk]
  push_cast
  ring
instance instFiniteFineBond : Finite 𝒮.FineBond :=
  Finite.of_injective (fun b => (b.source, b.dir)) (by
    rintro ⟨x, μ⟩ ⟨x', μ'⟩ h
    simp only [Prod.mk.injEq] at h
    rw [h.1, h.2])
theorem innerSum_isPos :
    IsPosPairing (innerSum : (𝒮.FineSite → ℝ) → (𝒮.FineSite → ℝ) → ℝ) :=
  isPosPairing_weightedSum (pow_pos 𝒮.ξ_pos 4)
variable {𝒮}
theorem blockAvg_add (f g : 𝒮.FineSite → ℝ) :
    blockAvg (f + g) = blockAvg f + blockAvg g := by apply _root_.YangMills.Construction.RegionSequence.GaugeProjections.blockAvg_add <;> assumption
theorem blockAvg_smul (r : ℝ) (f : 𝒮.FineSite → ℝ) :
    blockAvg (r • f) = r • blockAvg f := by apply _root_.YangMills.Construction.RegionSequence.GaugeProjections.blockAvg_smul <;> assumption
variable (𝒮) in
def avgKernelSubmodule : Submodule ℝ (𝒮.FineSite → ℝ) where
  carrier := 𝒮.avgKernel
  add_mem' := fun ha hb => ⟨𝒮.siteFns.add_mem ha.1 hb.1, by
    rw [blockAvg_add, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨𝒮.siteFns.zero_mem, by
    have := blockAvg_smul (𝒮 := 𝒮) 0 0
    simpa using this⟩
  smul_mem' := fun c _ ha => ⟨𝒮.siteFns.smul_mem c ha.1, by
    rw [blockAvg_smul, ha.2, smul_zero]⟩
theorem projSites_add (f g : 𝒮.FineSite → ℝ) :
    projSites (f + g) = projSites f + projSites g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.projSites_add <;> assumption
theorem projSites_smul (r : ℝ) (f : 𝒮.FineSite → ℝ) :
    projSites (r • f) = r • projSites f := by apply _root_.YangMills.Construction.RegionSequence.Positivity.projSites_smul <;> assumption
theorem latticeLaplacian_add (f g : 𝒮.FineSite → ℝ) :
    latticeLaplacian (f + g) = latticeLaplacian f + latticeLaplacian g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.latticeLaplacian_add <;> assumption
theorem latticeLaplacian_smul (r : ℝ) (f : 𝒮.FineSite → ℝ) :
    latticeLaplacian (r • f) = r • latticeLaplacian f := by apply _root_.YangMills.Construction.RegionSequence.Positivity.latticeLaplacian_smul <;> assumption
variable (𝒮) in
def dirichletLapLinear : (𝒮.FineSite → ℝ) →ₗ[ℝ] (𝒮.FineSite → ℝ) where
  toFun := dirichletLap
  map_add' f g := by
    simp only [dirichletLap, projSites_add, latticeLaplacian_add]
  map_smul' r f := by
    simp only [dirichletLap, projSites_smul, latticeLaplacian_smul, RingHom.id_apply]
variable (𝒮) in
def lapRange : Submodule ℝ (𝒮.FineSite → ℝ) :=
  (avgKernelSubmodule 𝒮).map (dirichletLapLinear 𝒮)
theorem lapRange_coe :
    (lapRange 𝒮 : Set (𝒮.FineSite → ℝ)) = dirichletLap '' 𝒮.avgKernel :=
  Submodule.map_coe _ _
theorem rangeProj_spec (f : 𝒮.FineSite → ℝ) :
    rangeProj f ∈ lapRange 𝒮 ∧
      ∀ w ∈ lapRange 𝒮, innerSum (f - rangeProj f) w = 0 := by
  have := (innerSum_isPos 𝒮).orthProjValue_spec (lapRange 𝒮) f
  rwa [lapRange_coe] at this
theorem rangeProj_eq {f r : 𝒮.FineSite → ℝ} (hr : r ∈ lapRange 𝒮)
    (hr' : ∀ w ∈ lapRange 𝒮, innerSum (f - r) w = 0) : rangeProj f = r := by
  obtain ⟨h₁, h₂⟩ := rangeProj_spec f
  refine (innerSum_isPos 𝒮).eq_of_forall_mem h₁ hr fun u hu => ?_
  have a := h₂ u hu
  have b := hr' u hu
  rw [(innerSum_isPos 𝒮).sub_left] at a b
  linarith
section Adjoint
variable (hadj : CellStructure.AdjointFacts 𝒮)
include hadj
end Adjoint
def bondBasis (b' : 𝒮.FineBond) : 𝒮.oneForms :=
  ⟨projBonds (indicator {b'} fun _ => (1 : ℝ)), fun _ hb => indicator_of_notMem hb _⟩
theorem weightedDist_comm (𝒮 : NestedRegions) (a b : 𝒮.Point) :
    𝒮.weightedDist a b = 𝒮.weightedDist b a := by apply _root_.YangMills.Construction.PartitionCubes.WeightedDistFromCube.weightedDist_comm <;> assumption
end LongOpBlocks
end YangMills.Construction
