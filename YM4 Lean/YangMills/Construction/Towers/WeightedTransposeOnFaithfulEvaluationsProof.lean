import YangMills.Construction.Towers.WeightedTransposeOnFaithfulEvaluations
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open PeriodicOperators (HasFiniteSupport KernelMatrix applyKernel unitKernel ApplySummable)
open RescaledConditions (TransposeKernelScaling linearMapKernel)
namespace FaithfulCoordinates
variable {r r' : PauliComponentsOfSymmetricKernel}
theorem eq_of_coeffs_eq (hr : IsFaithfulEvaluation r) {f g : r.space.index → Matrices.ComplexMatrix2}
    (hf : f ∈ r.space.complexSubmodule) (hg : g ∈ r.space.complexSubmodule)
    (h : r.coeffs f = r.coeffs g) : f = g := by
  rw [← hr.ofCoeffs_coeffs f hf, ← hr.ofCoeffs_coeffs g hg, h]
theorem coeffs_zero (hr : IsFaithfulEvaluation r) :
    r.coeffs (0 : r.space.index → Matrices.ComplexMatrix2) = 0 := by
  have h := hr.coeffs_linear 1 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
  simpa using h
def coeffsMap (hr : IsFaithfulEvaluation r) : r.space.complexSubmodule →ₗ[ℂ] (r.Index → ℂ) where
  toFun f := r.coeffs f
  map_add' f g := by
    have h := hr.coeffs_linear 1 f f.2 g g.2
    simpa using h
  map_smul' z f := by
    have h := hr.coeffs_linear z f f.2 0 (Submodule.zero_mem _)
    simpa [coeffs_zero hr] using h
theorem coeffsMap_apply (hr : IsFaithfulEvaluation r) (f : r.space.complexSubmodule) :
    coeffsMap hr f = r.coeffs f := rfl
def unitCoeffs (r : PauliComponentsOfSymmetricKernel) (i : r.Index) : r.Index → ℂ := fun j => unitKernel r.Index j i
theorem unitCoeffs_self (i : r.Index) : unitCoeffs r i i = 1 := by
  simp [unitCoeffs, unitKernel]
theorem unitCoeffs_of_ne {i j : r.Index} (h : j ≠ i) : unitCoeffs r i j = 0 := by
  simp [unitCoeffs, unitKernel, h]
def unitVector (hr : IsFaithfulEvaluation r) (i : r.Index) : r.space.complexSubmodule :=
  ⟨r.ofCoeffs (unitCoeffs r i), hr.ofCoeffs_mem _⟩
theorem coeffs_unitVector (hr : IsFaithfulEvaluation r) (i : r.Index) :
    r.coeffs (unitVector hr i) = unitCoeffs r i :=
  hr.coeffs_ofCoeffs _
theorem isFinitelySupported_unitVector (hr : IsFaithfulEvaluation r) (i : r.Index) :
    r.space.IsFinitelySupported (unitVector hr i) := by
  rw [hr.finitelySupported_iff _ (unitVector hr i).2, coeffs_unitVector]
  refine (Set.finite_singleton i).subset fun j hj => ?_
  by_contra hne
  exact hj (unitCoeffs_of_ne hne)
theorem eq_sum_unitVector (hr : IsFaithfulEvaluation r) (f : r.space.complexSubmodule)
    (s : Finset r.Index) (hs : ∀ i, r.coeffs f i ≠ 0 → i ∈ s) :
    f = ∑ i ∈ s, r.coeffs f i • unitVector hr i := by
  apply Subtype.ext
  apply eq_of_coeffs_eq hr f.2 (Subtype.property _)
  change coeffsMap hr f = coeffsMap hr _
  rw [map_sum]
  funext j
  have hu : ∀ i, coeffsMap hr (unitVector hr i) j = unitCoeffs r i j :=
    fun i => congrFun (coeffs_unitVector hr i) j
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hu]
  by_cases hj : j ∈ s
  · rw [Finset.sum_eq_single j (fun i _ hne => by rw [unitCoeffs_of_ne hne.symm, mul_zero])
      (fun h => absurd hj h), unitCoeffs_self, mul_one]
    rfl
  · have h0 : r.coeffs f j = 0 := by
      by_contra hne
      exact hj (hs j hne)
    rw [Finset.sum_eq_zero]
    · exact h0
    · intro i hi
      rw [unitCoeffs_of_ne (fun h : j = i => hj (by rw [h]; exact hi)), mul_zero]
theorem pair_unitVector (hr : IsFaithfulEvaluation r) (h : r.space.complexSubmodule) (i : r.Index) :
    r.space.pair h (unitVector hr i) = r.coeffs h i := by
  rw [hr.pair_eq _ h.2 _ (unitVector hr i).2 (isFinitelySupported_unitVector hr i),
    coeffs_unitVector, finsum_eq_single _ i
      (fun j hne => by rw [unitCoeffs_of_ne hne, mul_zero]), unitCoeffs_self, mul_one]
section Kernel
variable (hr : IsFaithfulEvaluation r) (hr' : IsFaithfulEvaluation r')
  (T : r.space.complexSubmodule →ₗ[ℂ] r'.space.complexSubmodule)
  (hT : PairedFunctionSpace.PreservesFiniteSupport T)
include hr in
theorem linearMapKernel_apply (i' : r'.Index) (i : r.Index) :
    linearMapKernel r r' T i' i = r'.coeffs (T (unitVector hr i)) i' := by
  unfold linearMapKernel
  exact dif_pos (hr.ofCoeffs_mem _)
include hr hr' hT in
theorem kernelColumn_finite (i : r.Index) : {i' | linearMapKernel r r' T i' i ≠ 0}.Finite := by
  have h : (Function.support (r'.coeffs (T (unitVector hr i)))).Finite :=
    (hr'.finitelySupported_iff _ (T (unitVector hr i)).2).1
      (hT _ (isFinitelySupported_unitVector hr i))
  refine h.subset fun i' hi' => ?_
  rw [Function.mem_support, ← linearMapKernel_apply hr]
  exact hi'
def kernelColumn (i : r.Index) : Finset r'.Index := (kernelColumn_finite hr hr' T hT i).toFinset
theorem mem_kernelColumn {i : r.Index} {i' : r'.Index} :
    i' ∈ kernelColumn hr hr' T hT i ↔ linearMapKernel r r' T i' i ≠ 0 := by
  simp [kernelColumn]
def columnPairing (g : r'.space.complexSubmodule) : r.Index → ℂ := fun i =>
  ∑ i' ∈ kernelColumn hr hr' T hT i, coeffsMap hr' g i' * linearMapKernel r r' T i' i
def transposeCandidate : r'.space.complexSubmodule →ₗ[ℂ] r.space.complexSubmodule where
  toFun g := ⟨r.ofCoeffs (columnPairing hr hr' T hT g), hr.ofCoeffs_mem _⟩
  map_add' g g' := by
    apply Subtype.ext
    apply eq_of_coeffs_eq hr (hr.ofCoeffs_mem _) (Subtype.property _)
    change _ = coeffsMap hr (_ + _)
    rw [map_add]
    change r.coeffs (r.ofCoeffs _) = r.coeffs (r.ofCoeffs _) + r.coeffs (r.ofCoeffs _)
    rw [hr.coeffs_ofCoeffs, hr.coeffs_ofCoeffs, hr.coeffs_ofCoeffs]
    funext i
    simp [columnPairing, add_mul, Finset.sum_add_distrib]
  map_smul' z g := by
    apply Subtype.ext
    apply eq_of_coeffs_eq hr (hr.ofCoeffs_mem _) (Subtype.property _)
    change _ = coeffsMap hr (z • _)
    rw [map_smul]
    change r.coeffs (r.ofCoeffs _) = z • r.coeffs (r.ofCoeffs _)
    rw [hr.coeffs_ofCoeffs, hr.coeffs_ofCoeffs]
    funext i
    simp [columnPairing, Finset.mul_sum, mul_assoc]
theorem coeffs_transposeCandidate (g : r'.space.complexSubmodule) :
    r.coeffs (transposeCandidate hr hr' T hT g) = columnPairing hr hr' T hT g :=
  hr.coeffs_ofCoeffs _
theorem transposeCandidate_isTransposeMap :
    PairedFunctionSpace.IsTransposeMap T (transposeCandidate hr hr' T hT) := by
  classical
  intro g f hf
  have hfin : (Function.support (r.coeffs f)).Finite := (hr.finitelySupported_iff f f.2).1 hf
  set s := hfin.toFinset with hs
  have hmem : ∀ i, r.coeffs f i ≠ 0 → i ∈ s := fun i h => by simpa [hs] using h
  have hTf : ∀ i', r'.coeffs (T f) i' =
      ∑ i ∈ s, r.coeffs f i * linearMapKernel r r' T i' i := by
    intro i'
    have h := congrArg (fun v => coeffsMap hr' (T v) i') (eq_sum_unitVector hr f s hmem)
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [coeffsMap_apply] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by rw [linearMapKernel_apply hr]; rfl
  rw [hr.pair_eq _ (transposeCandidate hr hr' T hT g).2 _ f.2 hf, coeffs_transposeCandidate,
    hr'.pair_eq _ g.2 _ (T f).2 (hT f hf)]
  rw [finsum_eq_sum_of_support_subset (s := s) _ (fun i hi => by
    refine hmem i fun h0 => hi ?_
    simp [h0])]
  set C := s.biUnion (kernelColumn hr hr' T hT) with hC
  rw [finsum_eq_sum_of_support_subset (s := C) _ (fun i' hi' => by
    by_contra hnot
    apply hi'
    have hz : r'.coeffs (T f) i' = 0 := by
      rw [hTf]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hk : linearMapKernel r r' T i' i = 0 := by
        by_contra hne
        exact hnot (by
          simp only [hC, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
          exact ⟨i, hi, (mem_kernelColumn hr hr' T hT).2 hne⟩)
      rw [hk, mul_zero]
    simp [hz])]
  simp only [hTf, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [columnPairing, Finset.sum_mul]
  have hsub : kernelColumn hr hr' T hT i ⊆ C := Finset.subset_biUnion_of_mem _ hi
  rw [Finset.sum_subset hsub (fun i' _ hnot => by
    have hk : linearMapKernel r r' T i' i = 0 := by
      by_contra hne
      exact hnot ((mem_kernelColumn hr hr' T hT).2 hne)
    rw [hk, mul_zero, zero_mul])]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [coeffsMap_apply]
  ring
include hr hr' hT in
theorem transposeMap_isTransposeMap :
    PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T) :=
  Classical.epsilon_spec (p := PairedFunctionSpace.IsTransposeMap T)
    ⟨_, transposeCandidate_isTransposeMap hr hr' T hT⟩
theorem coeffs_transposeMap (g : r'.space.complexSubmodule) (i : r.Index) :
    r.coeffs (PairedFunctionSpace.transposeMap T g : r.space.complexSubmodule) i =
      columnPairing hr hr' T hT g i := by
  rw [← pair_unitVector hr,
    transposeMap_isTransposeMap hr hr' T hT g _ (isFinitelySupported_unitVector hr i),
    hr'.pair_eq _ g.2 _ (T _).2 (hT _ (isFinitelySupported_unitVector hr i)),
    finsum_eq_sum_of_support_subset (s := kernelColumn hr hr' T hT i) _ (fun i' hi' => by
      rw [Finset.mem_coe, mem_kernelColumn, linearMapKernel_apply hr]
      intro h0
      apply hi'
      simp [h0])]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [linearMapKernel_apply hr]
  rfl
end Kernel
theorem transposeScales_holds : TransposeScales := by
  intro r r' hr hr' a a' T hT g
  have hzero : ∀ i i', i' ∉ kernelColumn hr hr' T hT i → linearMapKernel r r' T i' i = 0 := by
    intro i i' h
    by_contra hne
    exact h ((mem_kernelColumn hr hr' T hT).2 hne)
  have hw : ∀ (i : r.Index) (i' : r'.Index),
      meshTranspose a a' (linearMapKernel r r' T) i i' =
        (((a' ^ 4 * (a ^ 4)⁻¹ : ℝ)) : ℂ) * linearMapKernel r r' T i' i := by
    intro i i'
    simp [meshTranspose, PeriodicOperators.wTranspose, meshWeight, div_eq_mul_inv]
  refine ⟨fun i => ?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := kernelColumn hr hr' T hT i) fun i' hnot => ?_
    simp [hw, hzero i i' hnot]
  · funext i
    rw [Pi.smul_apply, coeffs_transposeMap hr hr' T hT, smul_eq_mul]
    unfold applyKernel
    rw [tsum_eq_sum (s := kernelColumn hr hr' T hT i) (fun i' h => by rw [hw, hzero i i' h]; simp)]
    simp only [columnPairing, Finset.mul_sum, hw]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [coeffsMap_apply]
    ring
end FaithfulCoordinates
end YangMills.Construction.Tower
end
