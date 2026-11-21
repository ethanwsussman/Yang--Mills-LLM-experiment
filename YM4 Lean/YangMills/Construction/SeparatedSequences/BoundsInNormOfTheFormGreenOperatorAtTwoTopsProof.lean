import YangMills.Construction.SeparatedSequences.BoundOfTheDifferencesOfTheExtensionKernelAtATopAndAnExpansionProof
import YangMills.Construction.SeparatedSequences.ClassSequenceHasASettingOfRegions
import YangMills.Construction.SeparatedSequences.PropagatorInASettingOfRegionsOfAClass
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.SeparatedClasses.ApexGreenBounds
open ClassData
section L2Sums
variable {ι : Type} [Fintype ι]
end L2Sums
section Norms
variable {C : ClassData} [Fintype C.BareBond]
theorem L_pos_real (C : ClassData) : (0 : ℝ) < C.L := by apply _root_.YangMills.Construction.SeparatedClasses.AnchorAgreementProof.cast_L_pos <;> assumption
theorem finestMesh_pos (C : ClassData) : 0 < finestMeshInLevelUnits C.L C.t :=
  zpow_pos (L_pos_real C) _
theorem bondInner_eq_sum (f g : C.BondFn) :
    C.bondInner f g = finestMeshInLevelUnits C.L C.t ^ 4 * ∑ b, f b * g b := by
  rw [ClassData.bondInner, latticeInner, finsum_eq_sum_of_fintype]
end Norms
section Restrictions
variable {C : ClassData} {X : Type}
open Classical in
def restrictTo (pick : C.BareBond → X) (z : X) (f : C.BondFn) : C.BondFn :=
  fun b => if pick b = z then f b else 0
end Restrictions
section Constants
variable {C : ClassData} {Ω : ℕ → Set C.Point}
end Constants
section Linearity
variable {C : ClassData} (Ω : ℕ → Set C.Point) (φ : BondFrame)
variable (C) in
def gradOneLinear : C.BondFn →ₗ[ℝ] C.Tensors 1 where
  toFun := C.gradOne
  map_add' f g := by
    funext ν b
    simp only [ClassData.gradOne, ClassData.bondFwd, Pi.add_apply]
    ring
  map_smul' a f := by
    funext ν b
    simp only [ClassData.gradOne, ClassData.bondFwd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
variable (C) in
def gradTwoLinear : C.Tensors 1 →ₗ[ℝ] C.Tensors 2 where
  toFun := C.gradTwo
  map_add' f g := by
    funext ν b
    simp only [ClassData.gradTwo, ClassData.bondFwd, Pi.add_apply]
    ring
  map_smul' a f := by
    funext ν b
    simp only [ClassData.gradTwo, ClassData.bondFwd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
variable [Fintype C.BareBond]
theorem bondInner_comm (f g : C.BondFn) : C.bondInner f g = C.bondInner g f := by
  simp only [bondInner_eq_sum, mul_comm (f _)]
def bondInnerLinear (u : C.BondFn) : C.BondFn →ₗ[ℝ] ℝ where
  toFun f := C.bondInner u f
  map_add' f g := by
    simp only [bondInner_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    simp only [bondInner_eq_sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
def tensorInnerLinear {r : ℕ} (K : C.Tensors r) : C.Tensors r →ₗ[ℝ] ℝ where
  toFun J := C.tensorInner K J
  map_add' J J' := by
    simp only [ClassData.tensorInner, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    exact (bondInnerLinear (K ν)).map_add (J ν) (J' ν)
  map_smul' a J := by
    simp only [ClassData.tensorInner, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    exact (bondInnerLinear (K ν)).map_smul a (J ν)
theorem tensorInner_comm {r : ℕ} (J K : C.Tensors r) :
    C.tensorInner J K = C.tensorInner K J := by
  simp only [ClassData.tensorInner]
  exact Finset.sum_congr rfl fun ν _ => bondInner_comm _ _
theorem exists_inner_representative (l : C.BondFn →ₗ[ℝ] ℝ) :
    ∃ v ∈ C.forms Ω φ, ∀ u ∈ C.forms Ω φ, C.bondInner v u = l u := by
  classical
  have hξ : finestMeshInLevelUnits C.L C.t ^ 4 ≠ 0 := pow_ne_zero 4 (finestMesh_pos C).ne'
  refine ⟨bondProjection C.cutoff (Ω 0) φ fun b =>
      (finestMeshInLevelUnits C.L C.t ^ 4)⁻¹ * l (Pi.single b 1),
    LinearMap.mem_range_self _ _, fun u hu => ?_⟩
  obtain ⟨w, rfl⟩ := hu
  set u : C.BondFn := bondProjection C.cutoff (Ω 0) φ w with hu
  have hsum : u = ∑ b, u b • (Pi.single b 1 : C.BondFn) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hl : l u = ∑ b, u b * l (Pi.single b 1) := by
    conv_lhs => rw [hsum]
    simp [map_sum]
  rw [hl, bondInner_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hv : ∀ f : C.BondFn, bondProjection C.cutoff (Ω 0) φ f b =
      (framedBonds C.cutoff (Ω 0) φ).indicator f b := fun _ => rfl
  rw [hv]
  by_cases hb : b ∈ framedBonds C.cutoff (Ω 0) φ
  · rw [Set.indicator_of_mem hb]
    have e : ∀ a x w : ℝ, a ≠ 0 → a * (a⁻¹ * x * w) = w * x := fun a x w h => by field_simp
    exact e _ _ _ hξ
  · have h0 : u b = 0 := by
      rw [hu]
      change (framedBonds C.cutoff (Ω 0) φ).indicator w b = 0
      exact Set.indicator_of_notMem hb _
    simp [h0]
theorem eq_of_inner_eq {v v' : C.BondFn} (hv : v ∈ C.forms Ω φ)
    (hv' : v' ∈ C.forms Ω φ)
    (h : ∀ u ∈ C.forms Ω φ, C.bondInner v u = C.bondInner v' u) : v = v' := by
  have hw := (C.forms Ω φ).sub_mem hv hv'
  have h0 : C.bondInner (v - v') (v - v') = 0 := by
    have e := (bondInnerLinear (v - v')).map_sub v v'
    change C.bondInner (v - v') (v - v') = C.bondInner (v - v') v - C.bondInner (v - v') v' at e
    rw [bondInner_comm (v - v') v, bondInner_comm (v - v') v'] at e
    rw [e, h _ hw, sub_self]
  rw [bondInner_eq_sum] at h0
  have h1 : ∑ b, (v - v') b * (v - v') b = 0 :=
    (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 4 (finestMesh_pos C).ne')
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => mul_self_nonneg ((v - v') b)).mp h1
  funext b
  have := mul_self_eq_zero.mp (h2 b (Finset.mem_univ b))
  exact sub_eq_zero.mp this
def formAdjoint {r : ℕ} (T : C.BondFn → C.Tensors r) (J : C.Tensors r) : C.BondFn :=
  RegionSequence.adjointValue (C.forms Ω φ : Set C.BondFn) C.bondInner C.tensorInner T J
theorem formAdjoint_spec {r : ℕ} (T : C.BondFn →ₗ[ℝ] C.Tensors r) (J : C.Tensors r) :
    formAdjoint Ω φ T J ∈ C.forms Ω φ ∧ ∀ u ∈ C.forms Ω φ,
      C.bondInner (formAdjoint Ω φ T J) u = C.tensorInner J (T u) :=
  Classical.epsilon_spec (p := fun v => v ∈ (C.forms Ω φ : Set C.BondFn) ∧
      ∀ u ∈ (C.forms Ω φ : Set C.BondFn), C.bondInner v u = C.tensorInner J (T u))
    (exists_inner_representative Ω φ (tensorInnerLinear J ∘ₗ T))
end Linearity
section NearCovers
variable {C : ClassData} {Ω : ℕ → Set C.Point}
variable [Fintype C.BareBond] {y y' : C.Apex Ω} {T : Finset (C.Apex Ω)}
  {pick : C.BareBond → C.Apex Ω}
end NearCovers
section SixBounds
variable {C : ClassData} {Ω : ℕ → Set C.Point}
theorem mesh_pos (y : C.Apex Ω) : 0 < y.mesh := zpow_pos (L_pos_real C) _
end SixBounds
section PropagatorEvaluation
open SingleSequence SingleSequence.SequenceData RegionSequence.NestedRegions
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions} {σ : s.data.BareSite ≃ 𝒮.FineSite}
  {β : s.data.BareBond ≃ 𝒮.FineBond}
theorem divOne_mem [Fintype s.data.BareBond] (J : s.data.Tensors 1) :
    s.data.divOne s.Ω s.frame J ∈ s.data.forms s.Ω s.frame :=
  (formAdjoint_spec s.Ω s.frame (gradOneLinear s.data) J).1
theorem divTwo_mem [Fintype s.data.BareBond] (J : s.data.Tensors 2) :
    s.data.divTwo s.Ω s.frame J ∈ s.data.forms s.Ω s.frame :=
  (formAdjoint_spec s.Ω s.frame (gradTwoLinear s.data ∘ₗ gradOneLinear s.data) J).1
variable {M : ℕ} {c : Propagator.PropagatorConstants}
end PropagatorEvaluation
end YangMills.Construction.SeparatedClasses.ApexGreenBounds
end
