import YangMills.Construction.Towers.KernelDeterminedByABilinearFormProof
import YangMills.Construction.Towers.KernelsOfPeriodicLocalBilinearMapsProof
import YangMills.Construction.Towers.FactsOnThePartsOfTheHessianOfTheWilsonActionProof
import YangMills.Construction.Towers.HessianOfTheWilsonAction
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicOperators YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Tower.WilsonHessianProof
def pauliCoeffLinear (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
  map_add' X Y := by fin_cases a <;> simp <;> ring
  map_smul' c X := by fin_cases a <;> simp <;> ring
theorem pauliCoeff_eq_linear {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a X = pauliCoeffLinear a X := by
  simp only [pauliCoeff, dif_pos h]
  rfl
theorem pauliCoeffLinear_pauliFamily (a a' : Fin 3) :
    pauliCoeffLinear a (ComplexMatrix2.pauliFamily a') = if a = a' then 1 else 0 := by
  fin_cases a <;> fin_cases a' <;>
    simp [pauliCoeffLinear, ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
      OneLoop.pauliZ]
  all_goals field_simp
  all_goals ring_nf
theorem ofPauliCoeffs_mem_traceless {σ : Type} (c : Fin 3 × σ → ℂ) (s : σ) :
    ofPauliCoeffs c s ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem sum_sq_pauliCoeffLinear {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeffLinear a X ^ 2 = ComplexMatrix2.halfTrace (X * X) := by
  have ht : X 1 1 = -X 0 0 := by
    have h0 : Matrix.trace X = 0 := h
    rw [Matrix.trace_fin_two] at h0
    linear_combination h0
  have hI : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  have hN : ComplexMatrix2.halfTrace (X * X) = X 0 0 ^ 2 + X 0 1 * X 1 0 := by
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, ht]
    ring
  rw [hN]
  simp only [Fin.sum_univ_three, pauliCoeffLinear, LinearMap.coe_mk, AddHom.coe_mk]
  simp
  field_simp
  ring_nf
  simp [hI]
  ring
section Local
variable {N N' : Type}
theorem exists_represents_of_finite_reads {J : Type} [Fintype J] (M : (N → ℂ) → N' → ℂ)
    (g : N' → J → N) (c : N' → J → ℂ) (h : ∀ f ι', M f ι' = ∑ j, c ι' j * f (g ι' j)) :
    ∃ T : KernelMatrix N N', Represents T M ∧ ∀ ι' ι, T ι' ι ≠ 0 → ∃ j, g ι' j = ι := by
  classical
  let T : KernelMatrix N N' := fun ι' ι => ∑ j, if g ι' j = ι then c ι' j else 0
  have hT : ∀ ι' ι, T ι' ι ≠ 0 → ∃ j, g ι' j = ι := by
    intro ι' ι hne
    by_contra hno
    push Not at hno
    exact hne (Finset.sum_eq_zero fun j _ => if_neg (hno j))
  have hzero : ∀ ι' ι, ι ∉ Finset.univ.image (g ι') → T ι' ι = 0 := by
    intro ι' ι hι
    by_contra hne
    obtain ⟨j, hj⟩ := hT ι' ι hne
    exact hι (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
  refine ⟨T, fun f => ⟨fun ι' => ?_, ?_⟩, hT⟩
  · refine (hasSum_sum_of_ne_finset_zero (s := Finset.univ.image (g ι')) fun ι hι => ?_).summable
    simp [hzero ι' ι hι]
  · funext ι'
    rw [h f ι']
    change ∑' ι, T ι' ι * f ι = _
    rw [tsum_eq_sum (s := Finset.univ.image (g ι')) fun ι hι => by simp [hzero ι' ι hι]]
    simp only [T, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (g ι' j)]
    · simp
    · intro ι _ hne
      simp [Ne.symm hne]
    · intro hno
      exact absurd (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩) hno
abbrev unitVec (ι : N) : N → ℂ := (basisFunction ι : finsuppFunctions N)
theorem unitVec_self (ι : N) : unitVec ι ι = 1 := by apply _root_.YangMills.Construction.Tower.PolarisedKernel.basisFunction_self <;> assumption
theorem unitVec_of_ne {ι x : N} (h : x ≠ ι) : unitVec ι x = 0 := by apply _root_.YangMills.Construction.Tower.PolarisedKernel.basisFunction_of_ne <;> assumption
theorem applyKernel_unitVec (T : KernelMatrix N N') (ι : N) (ι' : N') :
    applyKernel T (unitVec ι) ι' = T ι' ι := by apply _root_.YangMills.Construction.LocalKernels.LocalBilinearKernels.applyKernel_pointIndicator <;> assumption
theorem represents_unitVec {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ} (h : Represents T M)
    (ι : N) (ι' : N') : M (unitVec ι) ι' = T ι' ι := by
  rw [← (h (unitVec ι)).2, applyKernel_unitVec]
theorem represents_unitVec_add {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) (ι₁ ι₂ : N) (ι' : N') :
    M (unitVec ι₁ + unitVec ι₂) ι' = T ι' ι₁ + T ι' ι₂ := by
  classical
  rw [← (h _).2, ← applyKernel_unitVec T ι₁, ← applyKernel_unitVec T ι₂]
  change ∑' x, T ι' x * (unitVec ι₁ x + unitVec ι₂ x) =
    ∑' x, T ι' x * unitVec ι₁ x + ∑' x, T ι' x * unitVec ι₂ x
  have s : ∀ ι : N, Summable fun x => T ι' x * unitVec ι x := fun ι => by
    refine (hasSum_sum_of_ne_finset_zero (s := {ι}) fun x hx => ?_).summable
    have hx' : x ≠ ι := by simpa using hx
    change T ι' x * (if x = ι then 1 else 0) = 0
    simp [hx']
  rw [← (s ι₁).tsum_add (s ι₂)]
  simp only [mul_add]
theorem kernelOfMap_eq {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ} (h : Represents T M) :
    kernelOfMap M = T := by apply _root_.YangMills.Construction.Tower.FullSpace.RescaledTrivialRelationsProof.kernelOfMap_eq <;> assumption
end Local
section Faces
variable {σ Pl : Type}
def fourEdgeMap (bnd : Pl → Fin 4 → σ) (C : Pl → Fin 4 → ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2)
    (f : Fin 3 × σ → ℂ) : Fin 3 × Pl → ℂ :=
  fun κ => pauliCoeff κ.1 (∑ i, C κ.2 i (ofPauliCoeffs f (bnd κ.2 i)))
theorem exists_represents_fourEdgeMap (bnd : Pl → Fin 4 → σ)
    (C : Pl → Fin 4 → ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2)
    (hC : ∀ p i X, X ∈ ComplexMatrix2.traceless → C p i X ∈ ComplexMatrix2.traceless) :
    ∃ T : KernelMatrix (Fin 3 × σ) (Fin 3 × Pl), Represents T (fourEdgeMap bnd C) ∧
      ∀ κ ι, T κ ι ≠ 0 → ∃ i, bnd κ.2 i = ι.2 := by
  obtain ⟨T, hT, hs⟩ := exists_represents_of_finite_reads (J := Fin 4 × Fin 3) (fourEdgeMap bnd C)
    (fun κ j => (j.2, bnd κ.2 j.1))
    (fun κ j => pauliCoeffLinear κ.1 (C κ.2 j.1 (ComplexMatrix2.pauliFamily j.2)))
    (fun f κ => by
      have hmem : (∑ i, C κ.2 i (ofPauliCoeffs f (bnd κ.2 i))) ∈ ComplexMatrix2.traceless :=
        ComplexMatrix2.traceless.sum_mem fun i _ => hC _ _ _ (ofPauliCoeffs_mem_traceless _ _)
      change pauliCoeff κ.1 _ = _
      rw [pauliCoeff_eq_linear hmem]
      simp only [map_sum, Fintype.sum_prod_type, ofPauliCoeffs, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => mul_comm _ _)
  refine ⟨T, hT, fun κ ι hne => ?_⟩
  obtain ⟨j, hj⟩ := hs κ ι hne
  exact ⟨j.1, by rw [← hj]⟩
def pointwiseMul (z : Pl → ℂ) (f : Fin 3 × Pl → ℂ) : Fin 3 × Pl → ℂ :=
  fun κ => pauliCoeff κ.1 (z κ.2 • ofPauliCoeffs f κ.2)
theorem pointwiseMul_apply (z : Pl → ℂ) (f : Fin 3 × Pl → ℂ) (κ : Fin 3 × Pl) :
    pointwiseMul z f κ = z κ.2 * f κ := by
  have hmem := ComplexMatrix2.traceless.smul_mem (z κ.2) (ofPauliCoeffs_mem_traceless f κ.2)
  change pauliCoeff κ.1 _ = _
  rw [pauliCoeff_eq_linear hmem]
  simp only [map_smul, smul_eq_mul, ofPauliCoeffs, map_sum, pauliCoeffLinear_pauliFamily, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
theorem represents_pointwiseMul (z : Pl → ℂ) :
    Represents (I := Fin 3 × Pl) (J := Fin 3 × Pl) (fun κ κ' => open Classical in if κ' = κ then z κ.2 else 0)
      (pointwiseMul z) := by
  classical
  intro f
  refine ⟨fun κ => ?_, ?_⟩
  · refine (hasSum_sum_of_ne_finset_zero (s := {κ}) fun x hx => ?_).summable
    have hx' : x ≠ κ := by simpa using hx
    simp [hx']
  · funext κ
    rw [pointwiseMul_apply]
    change ∑' x, (if x = κ then z κ.2 else 0) * f x = _
    rw [tsum_eq_single κ fun x hx => by simp [hx]]
    simp
end Faces
section Core
variable {σ Pl : Type}
def weightedSquareSum (z : Pl → ℂ) (M₁ M₂ : Fin 3 × Pl → ℂ) : ℂ :=
  ∑ᶠ p, z p * ∑ a, (M₁ (a, p) + M₂ (a, p)) ^ 2
theorem meshTranspose_apply {S S' : Type} {η : ℝ} (hη : η ≠ 0)
    (T : KernelMatrix (Fin 3 × S) (Fin 3 × S')) (ι : Fin 3 × S) (κ : Fin 3 × S') :
    meshTranspose η η T ι κ = T κ ι := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.meshTranspose_self <;> assumption
theorem kernel_eq_of_quadratic (η : ℝ) (hη : η ≠ 0) (bnd : Pl → Fin 4 → σ)
    (hfin : ∀ s, {p | ∃ i, bnd p i = s}.Finite)
    {K₁ K₂ : KernelMatrix (Fin 3 × σ) (Fin 3 × Pl)} {M₁ M₂ : (Fin 3 × σ → ℂ) → Fin 3 × Pl → ℂ}
    (h₁ : Represents K₁ M₁) (h₂ : Represents K₂ M₂)
    (hs₁ : ∀ κ ι, K₁ κ ι ≠ 0 → ∃ i, bnd κ.2 i = ι.2)
    (hs₂ : ∀ κ ι, K₂ κ ι ≠ 0 → ∃ i, bnd κ.2 i = ι.2)
    (z : Pl → ℂ) {Zk : KernelMatrix (Fin 3 × Pl) (Fin 3 × Pl)}
    (hZ : ∀ κ κ', Zk κ κ' = open Classical in if κ' = κ then z κ.2 else 0)
    (H Fk : KernelMatrix (Fin 3 × σ) (Fin 3 × σ))
    (hdiag : ∀ ι, H ι ι = weightedSquareSum z (M₁ (unitVec ι)) (M₂ (unitVec ι)) + Fk ι ι)
    (hoff : ∀ ι ι', H ι ι + H ι' ι' + 2 * H ι ι' =
      weightedSquareSum z (M₁ (unitVec ι + unitVec ι')) (M₂ (unitVec ι + unitVec ι')) +
        (Fk ι ι + Fk ι' ι' + 2 * Fk ι ι')) :
    H = compKernel (meshTranspose η η (K₁ + K₂)) (compKernel Zk (K₁ + K₂)) + Fk := by
  classical
  set A := K₁ + K₂ with hA
  have hAe : ∀ κ ι, A κ ι = K₁ κ ι + K₂ κ ι := fun _ _ => rfl
  have hAs : ∀ κ ι, A κ ι ≠ 0 → ∃ i, bnd κ.2 i = ι.2 := by
    intro κ ι hne
    by_contra hno
    have e₁ : K₁ κ ι = 0 := by
      by_contra h
      exact hno (hs₁ κ ι h)
    have e₂ : K₂ κ ι = 0 := by
      by_contra h
      exact hno (hs₂ κ ι h)
    exact hne (by rw [hAe, e₁, e₂, add_zero])
  have hZA : ∀ κ ι, compKernel Zk A κ ι = z κ.2 * A κ ι := by
    intro κ ι
    change ∑' κ', Zk κ κ' * A κ' ι = _
    rw [tsum_eq_single κ fun x hx => by simp [hZ, hx]]
    simp [hZ]
  have hP : ∀ (ι ι' : Fin 3 × σ) (S : Finset Pl), (∀ p, (∃ i, bnd p i = ι.2) → p ∈ S) →
      compKernel (meshTranspose η η A) (compKernel Zk A) ι ι' =
        ∑ p ∈ S, z p * ∑ a, A (a, p) ι * A (a, p) ι' := by
    intro ι ι' S hS
    change ∑' κ, meshTranspose η η A ι κ * compKernel Zk A κ ι' = _
    simp only [meshTranspose_apply hη, hZA]
    rw [tsum_eq_sum (s := Finset.univ ×ˢ S)]
    · rw [Finset.sum_product_right]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    · intro κ hκ
      have e : A κ ι = 0 := by
        by_contra hne
        exact hκ (Finset.mem_product.mpr ⟨Finset.mem_univ _, hS _ (hAs κ ι hne)⟩)
      simp [e]
  have hR₁ : ∀ (ι : Fin 3 × σ) (S : Finset Pl), (∀ p, (∃ i, bnd p i = ι.2) → p ∈ S) →
      weightedSquareSum z (M₁ (unitVec ι)) (M₂ (unitVec ι)) =
        ∑ p ∈ S, z p * ∑ a, A (a, p) ι ^ 2 := by
    intro ι S hS
    have e : ∀ p, z p * ∑ a, (M₁ (unitVec ι) (a, p) + M₂ (unitVec ι) (a, p)) ^ 2 =
        z p * ∑ a, A (a, p) ι ^ 2 := fun p => by
      simp only [represents_unitVec h₁, represents_unitVec h₂, hAe]
    simp only [weightedSquareSum, e]
    refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
    by_contra hno
    refine hp ?_
    have hz : ∀ a, A (a, p) ι = 0 := fun a => by
      by_contra hne
      exact hno (hS _ (hAs (a, p) ι hne))
    simp [hz]
  have hR₂ : ∀ (ι ι' : Fin 3 × σ) (S : Finset Pl),
      (∀ p, ((∃ i, bnd p i = ι.2) ∨ ∃ i, bnd p i = ι'.2) → p ∈ S) →
      weightedSquareSum z (M₁ (unitVec ι + unitVec ι')) (M₂ (unitVec ι + unitVec ι')) =
        ∑ p ∈ S, z p * ∑ a, (A (a, p) ι + A (a, p) ι') ^ 2 := by
    intro ι ι' S hS
    have e : ∀ p, z p * ∑ a, (M₁ (unitVec ι + unitVec ι') (a, p) +
        M₂ (unitVec ι + unitVec ι') (a, p)) ^ 2 =
        z p * ∑ a, (A (a, p) ι + A (a, p) ι') ^ 2 := fun p => by
      simp only [represents_unitVec_add h₁, represents_unitVec_add h₂, hAe]
      congr 1
      exact Finset.sum_congr rfl fun a _ => by ring
    simp only [weightedSquareSum, e]
    refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
    by_contra hno
    refine hp ?_
    have hz : ∀ a, A (a, p) ι = 0 ∧ A (a, p) ι' = 0 := fun a => by
      constructor
      · by_contra hne
        exact hno (hS _ (Or.inl (hAs (a, p) ι hne)))
      · by_contra hne
        exact hno (hS _ (Or.inr (hAs (a, p) ι' hne)))
    simp [fun a => (hz a).1, fun a => (hz a).2]
  funext ι ι'
  let S : Finset Pl := (hfin ι.2).toFinset ∪ (hfin ι'.2).toFinset
  have hS₁ : ∀ p, (∃ i, bnd p i = ι.2) → p ∈ S := fun p h =>
    Finset.mem_union_left _ ((hfin ι.2).mem_toFinset.mpr h)
  have hS₂ : ∀ p, (∃ i, bnd p i = ι'.2) → p ∈ S := fun p h =>
    Finset.mem_union_right _ ((hfin ι'.2).mem_toFinset.mpr h)
  have hd₁ := hdiag ι
  have hd₂ := hdiag ι'
  have ho := hoff ι ι'
  rw [hR₁ ι S hS₁] at hd₁
  rw [hR₁ ι' S hS₂] at hd₂
  rw [hR₂ ι ι' S (fun p h => h.elim (hS₁ p) (hS₂ p))] at ho
  have hexp : ∑ p ∈ S, z p * ∑ a, (A (a, p) ι + A (a, p) ι') ^ 2 =
      ∑ p ∈ S, z p * ∑ a, A (a, p) ι ^ 2 + ∑ p ∈ S, z p * ∑ a, A (a, p) ι' ^ 2 +
        2 * ∑ p ∈ S, z p * ∑ a, A (a, p) ι * A (a, p) ι' := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Fin.sum_univ_three]
    ring
  rw [hexp] at ho
  change H ι ι' = compKernel (meshTranspose η η A) (compKernel Zk A) ι ι' + Fk ι ι'
  rw [hP ι ι' S hS₁]
  linear_combination (1 / 2 : ℂ) * ho - (1 / 2 : ℂ) * hd₁ - (1 / 2 : ℂ) * hd₂
end Core
section Forms
variable {N : Type}
theorem kernelPairing_unitVec (w : N → ℝ) (X : KernelMatrix N N) (ι : N) :
    kernelPairing w X (unitVec ι) (unitVec ι) = (w ι : ℂ) * X ι ι := by
  classical
  unfold kernelPairing
  rw [finsum_eq_single _ (ι, ι)]
  · change (w ι : ℂ) * (if ι = ι then 1 else 0) * X ι ι * (if ι = ι then 1 else 0) = _
    simp
  · rintro ⟨x, y⟩ hxy
    change (w x : ℂ) * (if x = ι then 1 else 0) * X x y * (if y = ι then 1 else 0) = 0
    by_cases hx : x = ι
    · have hy : y ≠ ι := fun hy => hxy (by rw [hx, hy])
      simp [hy]
    · simp [hx]
theorem kernelPairing_unitVec_add (w : ℝ) (X : KernelMatrix N N) (hX : ∀ ι ι', X ι ι' = X ι' ι)
    (ι ι' : N) :
    kernelPairing (fun _ => w) X (unitVec ι + unitVec ι') (unitVec ι + unitVec ι') =
      (w : ℂ) * (X ι ι + X ι' ι' + 2 * X ι ι') := by
  classical
  unfold kernelPairing
  let g : N → ℂ := unitVec ι + unitVec ι'
  have hg : ∀ x, x ≠ ι → x ≠ ι' → g x = 0 := fun x h h' => by
    change (if x = ι then (1 : ℂ) else 0) + (if x = ι' then 1 else 0) = 0
    simp [h, h']
  change ∑ᶠ p : N × N, (w : ℂ) * g p.1 * X p.1 p.2 * g p.2 = _
  let S : Finset N := {ι, ι'}
  rw [finsum_eq_sum_of_support_subset (s := S ×ˢ S) _ (fun p hp => by
    have h₁ : p.1 ∈ S := by
      by_contra hno
      refine hp ?_
      have : g p.1 = 0 := hg _ (fun e => hno (by simp [S, e])) (fun e => hno (by simp [S, e]))
      simp [this]
    have h₂ : p.2 ∈ S := by
      by_contra hno
      refine hp ?_
      have : g p.2 = 0 := hg _ (fun e => hno (by simp [S, e])) (fun e => hno (by simp [S, e]))
      simp [this]
    exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨h₁, h₂⟩))]
  rw [Finset.sum_product]
  by_cases e : ι = ι'
  · subst e
    have h2 : g ι = 2 := by
      change (if ι = ι then (1 : ℂ) else 0) + (if ι = ι then 1 else 0) = 2
      norm_num
    simp only [S, Finset.pair_eq_singleton, Finset.sum_singleton, h2]
    ring
  · have g₁ : g ι = 1 := by
      change (if ι = ι then (1 : ℂ) else 0) + (if ι = ι' then 1 else 0) = 1
      simp [e]
    have g₂ : g ι' = 1 := by
      change (if ι' = ι then (1 : ℂ) else 0) + (if ι' = ι' then 1 else 0) = 1
      simp [Ne.symm e]
    simp only [S, Finset.sum_pair e, g₁, g₂]
    rw [hX ι' ι]
    ring
end Forms
theorem support_const_mul_finite {α : Type} (c : ℂ) {g : α → ℂ}
    (h : (Function.support g).Finite) :
    (Function.support fun p => c * g p).Finite :=
  h.subset fun p hp h0 => hp (by
    change c * g p = 0
    rw [show g p = 0 from h0, mul_zero])
theorem polarization_step {c R F q₁₁ q₂₂ q₁₂ q₂₁ : ℂ} (hc : c ≠ 0)
    (h : q₁₁ + q₁₂ + (q₂₁ + q₂₂) = c * R + c * F) (hs : q₂₁ = q₁₂) :
    c⁻¹ * q₁₁ + c⁻¹ * q₂₂ + 2 * (c⁻¹ * q₁₂) = R + F := by
  subst hs
  field_simp
  linear_combination h
theorem real_smul_eq_complex_smul (η : ℝ) (X : ComplexMatrix2) : η • X = (η : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
def conjugateLinear (V : ComplexMatrix2) : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 where
  toFun X := ComplexMatrix2.conjugateBy V X
  map_add' X Y := by simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
  map_smul' c X := by simp [ComplexMatrix2.conjugateBy]
theorem conjugateLinear_apply (V X : ComplexMatrix2) :
    conjugateLinear V X = ComplexMatrix2.conjugateBy V X := rfl
theorem conj_mem_traceless {V X : ComplexMatrix2} (hV : V.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
def coboundaryCoeff (η : ℝ) (i : Fin 4) : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 :=
  ((η : ℂ)⁻¹ * transportSign i) • LinearMap.id
def defectCoeff (η : ℝ) (T : Fin 4 → ComplexMatrix2) (i : Fin 4) :
    ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 :=
  ((η : ℂ)⁻¹ * transportSign i) • (conjugateLinear (T i) - LinearMap.id)
theorem coboundaryCoeff_mem (η : ℝ) (i : Fin 4) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) : coboundaryCoeff η i X ∈ ComplexMatrix2.traceless :=
  ComplexMatrix2.traceless.smul_mem _ hX
theorem defectCoeff_mem (η : ℝ) {T : Fin 4 → ComplexMatrix2} (hT : ∀ i, (T i).det = 1)
    (i : Fin 4) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    defectCoeff η T i X ∈ ComplexMatrix2.traceless :=
  ComplexMatrix2.traceless.smul_mem _
    (ComplexMatrix2.traceless.sub_mem (conj_mem_traceless (hT i) hX) hX)
theorem secondDerivExpr_smul (y : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) {η : ℝ}
    (hη : η ≠ 0) (X : ComplexMatrix2) (hX : X ∈ ComplexMatrix2.traceless)
    (hy : ∑ i, y i = η • X) :
    FaceTermDerivatives.secondDerivExpr (fun i => η • y i) W =
      (η : ℂ) ^ 4 * ((1 / 2 * ComplexMatrix2.fullTrace W) * ∑ a, pauliCoeffLinear a X ^ 2) +
        (η : ℂ) ^ 4 * ((Complex.I / 2) * ComplexMatrix2.fullTrace (bracketSumOrdered y y *
          ((1 / (2 * Complex.I * (η : ℂ) ^ 2)) • (W - W⁻¹)))) := by
  have hηc : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  have hs : ∑ i, η • y i = ((η : ℂ) ^ 2) • X := by
    rw [← Finset.smul_sum, hy, real_smul_eq_complex_smul, real_smul_eq_complex_smul, smul_smul, sq]
  have hc : FaceTermDerivatives.commutatorSum (fun i => η • y i) =
      ((η : ℂ) ^ 2) • bracketSumOrdered y y := by
    simp only [FaceTermDerivatives.commutatorSum, bracketSumOrdered, Finset.smul_sum,
      real_smul_eq_complex_smul, smul_sub, smul_mul_smul_comm, sq]
  rw [sum_sq_pauliCoeffLinear hX]
  simp only [FaceTermDerivatives.secondDerivExpr, hs, hc]
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_smul, smul_eq_mul, mul_smul_comm, smul_mul_assoc]
  field_simp
  ring
section FiniteSide
variable {L n k : ℕ}
theorem faceEdge_isPositivelyOriented (p : Face L n k 0) (i : Fin 4) :
    (faceEdge p i).IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.CurvatureHessianFacts.faceEdge_isPositivelyOriented <;> assumption
def positiveFaceEdge (p : Face L n k 0) (i : Fin 4) : PositiveEdge L n k 0 :=
  ⟨faceEdge p i, faceEdge_isPositivelyOriented p i⟩
theorem faceEdge_mem_faceEdges (p : Face L n k 0) (i : Fin 4) :
    faceEdge p i ∈ faceEdges p :=
  List.getElem_mem _
theorem small_multiple_meshSize_ne_zero (hL : 13 ≤ L) (hn : 0 < n) {c : ℕ} (hc : c = 1 ∨ c = 2) :
    ((((c : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k 0) : ℝ)) :
      AddCircle (PeriodicLattice.torusSide L n)) ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff _).mp h
  have e : (m : ℝ) * (2 * (L : ℝ) ^ (n + k)) = c := by
    have hs : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k 0) = ((L : ℝ) ^ k)⁻¹ := by
      simp [PeriodicLattice.meshSize, PeriodicLattice.levelDepth, zpow_neg]
    rw [hs, zsmul_eq_mul, PeriodicLattice.torusSide] at hm
    rw [pow_add, ← mul_assoc, ← mul_assoc, mul_assoc (m : ℝ), hm]
    field_simp
  have e' : m * (2 * (L : ℤ) ^ (n + k)) = c := by exact_mod_cast e
  have hdvd : (L : ℤ) ∣ c := by
    refine ⟨m * (2 * (L : ℤ) ^ (n + k - 1)), ?_⟩
    rw [← e', show n + k = (n + k - 1) + 1 by omega, pow_succ]
    simp only [Nat.add_sub_cancel]
    ring
  have hle : (L : ℤ) ≤ c := Int.le_of_dvd (by rcases hc with rfl | rfl <;> norm_num) hdvd
  rcases hc with rfl | rfl <;> omega
theorem not_isPositivelyOriented_opposite (hL : 13 ≤ L) (hn : 0 < n) {b : Edge L n k 0}
    (h : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := h
  rintro ⟨ν, hν⟩
  have hν' : b.source - b.target = PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) ν :=
    hν
  have hsum : PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) μ +
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) ν = 0 := by
    rw [← hμ, ← hν']
    abel
  have hc := congrArg (fun x : Vertex L n k 0 => (x : PeriodicLattice.FourTorus L n) μ) hsum
  by_cases e : ν = μ
  · subst e
    refine small_multiple_meshSize_ne_zero (k := k) hL hn (c := 2) (Or.inr rfl) ?_
    simpa [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, two_mul, add_mul] using hc
  · refine small_multiple_meshSize_ne_zero (k := k) hL hn (c := 1) (Or.inl rfl) ?_
    simpa [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne (Ne.symm e)]
      using hc
theorem opposite_isPositivelyOriented_of_not {b : Edge L n k 0} (h : ¬b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, e | e⟩ := b.isNeighbour
  · exact absurd ⟨μ, e⟩ h
  · refine ⟨μ, ?_⟩
    change b.source - b.target = _
    rw [← neg_sub, e, neg_neg]
abbrev coeffForm (f : Fin 3 × PositiveEdge L n k 0 → ℂ) : Edge L n k 0 → ComplexMatrix2 :=
  (edgePauliCoordinates L n k 0).ofCoeffs f
theorem coeffForm_apply (f : Fin 3 × PositiveEdge L n k 0 → ℂ) {b : Edge L n k 0}
    (h : b.IsPositivelyOriented) : coeffForm f b = ofPauliCoeffs f ⟨b, h⟩ := by apply _root_.YangMills.Construction.Tower.CurvatureHessianFacts.edgeField_apply <;> assumption
theorem coeffForm_mem (hL : 13 ≤ L) (hn : 0 < n) (f : Fin 3 × PositiveEdge L n k 0 → ℂ) :
    coeffForm f ∈ complexEdgeForms L n k 0 := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [coeffForm_apply f hb]
    exact ofPauliCoeffs_mem_traceless _ _
  · by_cases hb : b.IsPositivelyOriented
    · have hr := not_isPositivelyOriented_opposite hL hn hb
      rw [coeffForm_apply f hb]
      have hb' : b.opposite.opposite.IsPositivelyOriented := hb
      simp only [coeffForm, edgePauliCoordinates, extendOddly, if_neg hr, dif_pos hb']
      rfl
    · have hr := opposite_isPositivelyOriented_of_not hb
      rw [coeffForm_apply f hr]
      simp [coeffForm, edgePauliCoordinates, extendOddly, hb, hr]
theorem basisForm_eq_coeffForm (ι : Fin 3 × PositiveEdge L n k 0) :
    basisForm ι.1 ι.2 = coeffForm (unitVec ι) := by
  classical
  simp only [basisForm, coeffForm, edgePauliCoordinates]
  congr 1
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [dif_pos hb]
    simp only [ofPauliCoeffs]
    by_cases e : b = ι.2.1
    · rw [if_pos e]
      rw [Finset.sum_eq_single ι.1]
      · have : (ι.1, (⟨b, hb⟩ : PositiveEdge L n k 0)) = ι := Prod.ext rfl (Subtype.ext e)
        rw [this, unitVec_self, one_smul]
      · intro a _ ha
        have : (a, (⟨b, hb⟩ : PositiveEdge L n k 0)) ≠ ι := fun h => ha (congrArg Prod.fst h)
        rw [unitVec_of_ne this, zero_smul]
      · simp
    · rw [if_neg e]
      symm
      refine Finset.sum_eq_zero fun a _ => ?_
      have : (a, (⟨b, hb⟩ : PositiveEdge L n k 0)) ≠ ι := fun h =>
        e (congrArg Subtype.val (congrArg Prod.snd h))
      rw [unitVec_of_ne this, zero_smul]
  · rw [dif_neg hb, if_neg]
    intro e
    exact hb (e ▸ ι.2.2)
theorem coeffForm_add (f g : Fin 3 × PositiveEdge L n k 0 → ℂ) :
    coeffForm (f + g) = coeffForm f + coeffForm g := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [Pi.add_apply, coeffForm_apply _ hb, ofPauliCoeffs, add_smul, Finset.sum_add_distrib]
  · have hr := opposite_isPositivelyOriented_of_not hb
    simp only [coeffForm, edgePauliCoordinates, extendOddly, Pi.add_apply, if_neg hb, dif_pos hr,
      ofPauliCoeffs, add_smul, Finset.sum_add_distrib, neg_add]
theorem scaledEdgeCoboundary_eq_sum (b : Edge L n k 0 → ComplexMatrix2) (p : Face L n k 0) :
    scaledEdgeCoboundary b p =
      ∑ i, coboundaryCoeff (finestMesh L k) i (b (faceEdge p i)) := by
  simp only [scaledEdgeCoboundary, Pi.smul_apply, edgeCoboundary, coboundaryCoeff,
    LinearMap.smul_apply, LinearMap.id_apply, Fin.sum_univ_four, transportSign,
    real_smul_eq_complex_smul]
  simp only [faceEdge, faceEdges, finestMesh]
  simp [smul_add, mul_neg, neg_smul, sub_eq_add_neg, add_assoc, Complex.ofReal_inv]
theorem holonomyDefect_eq_sum (U b : Edge L n k 0 → ComplexMatrix2) (p : Face L n k 0) :
    holonomyDefect U b p =
      ∑ i, defectCoeff (finestMesh L k) (faceTransports U p) i (b (faceEdge p i)) := by
  simp only [holonomyDefect, defectCoeff, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, conjugateLinear_apply, real_smul_eq_complex_smul, Finset.smul_sum,
    smul_smul, Complex.ofReal_inv]
theorem sum_transportedForm (U b : Edge L n k 0 → ComplexMatrix2) (p : Face L n k 0)
    (hη : finestMesh L k ≠ 0) :
    ∑ i, transportedForm U b p i =
      finestMesh L k • (scaledEdgeCoboundary b p + holonomyDefect U b p) := by
  have hηc : (finestMesh L k : ℂ) ≠ 0 := by exact_mod_cast hη
  rw [scaledEdgeCoboundary_eq_sum, holonomyDefect_eq_sum, ← Finset.sum_add_distrib,
    real_smul_eq_complex_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [transportedForm, coboundaryCoeff, defectCoeff, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.id_apply, conjugateLinear_apply, ← smul_add, add_sub_cancel,
    smul_smul]
  rw [← mul_assoc, mul_inv_cancel₀ hηc, one_mul]
end FiniteSide
section FiniteSide
variable {L n k : ℕ}
theorem real_smul_mem_complexEdgeForms {b : Edge L n k 0 → ComplexMatrix2}
    (hb : b ∈ complexEdgeForms L n k 0) (c : ℝ) :
    c • b ∈ complexEdgeForms L n k 0 := by
  have e : c • b = (c : ℂ) • b := by
    funext x
    exact real_smul_eq_complex_smul _ _
  rw [e]
  exact Submodule.smul_mem _ _ hb
theorem transportedForm_smul (U b : Edge L n k 0 → ComplexMatrix2) (c : ℝ) (p : Face L n k 0) :
    transportedForm U (c • b) p = fun i => c • transportedForm U b p i := by
  funext i
  simp only [transportedForm, Pi.smul_apply, ComplexMatrix2.conjugateBy, real_smul_eq_complex_smul,
    mul_smul_comm, smul_mul_assoc]
  rw [smul_comm]
theorem remainderGaugeField_mem
    (hdet : ∀ Z : ComplexMatrix2,
      (ComplexMatrix2.matExp Z).det = Complex.exp (ComplexMatrix2.fullTrace Z))
    (hL : 13 ≤ L) (hn : 0 < n) {a : Edge L n k 0 → ComplexMatrix2}
    (ha : a ∈ complexEdgeForms L n k 0) :
    remainderGaugeField a ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup := by
  have hA := real_smul_mem_complexEdgeForms ha (finestMesh L k)
  have hvp : ∀ b : Edge L n k 0, b.IsPositivelyOriented →
      remainderGaugeField a b =
        ComplexMatrix2.matExp (Complex.I • (finestMesh L k • a) b) := fun b hb => by
    simp [remainderGaugeField, scaledRemainderForm, IdentityExpChart.expForm,
      PeriodicLattice.expTwist, hb]
  have hneg : ∀ b : Edge L n k 0, ¬b.IsPositivelyOriented →
      remainderGaugeField a b =
        (ComplexMatrix2.matExp (Complex.I • (finestMesh L k • a) b.opposite))⁻¹ := fun b hb => by
    simp [remainderGaugeField, scaledRemainderForm, IdentityExpChart.expForm,
      PeriodicLattice.expTwist, hb]
  have hd : ∀ b : Edge L n k 0, b.IsPositivelyOriented →
      (ComplexMatrix2.matExp (Complex.I • (finestMesh L k • a) b)).det = 1 := fun b hb => by
    have ht : Matrix.trace ((finestMesh L k • a) b) = 0 := hA.1 b hb
    rw [hdet]
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul, ht, smul_zero, Complex.exp_zero]
  have hu : ∀ b : Edge L n k 0, b.IsPositivelyOriented →
      IsUnit (ComplexMatrix2.matExp (Complex.I • (finestMesh L k • a) b)).det := fun b hb => by
    rw [hd b hb]
    exact isUnit_one
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [hvp b hb]
      exact hd b hb
    · rw [hneg b hb]
      change Matrix.det _ = 1
      rw [Matrix.det_nonsing_inv, hd _ (opposite_isPositivelyOriented_of_not hb)]
      simp
  · by_cases hb : b.IsPositivelyOriented
    · rw [hvp b hb, hneg _ (not_isPositivelyOriented_opposite hL hn hb)]
      rfl
    · rw [hneg b hb, hvp _ (opposite_isPositivelyOriented_of_not hb),
        Matrix.nonsing_inv_nonsing_inv _ (hu _ (opposite_isPositivelyOriented_of_not hb))]
theorem faceTransports_det {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup) (p : Face L n k 0)
    (i : Fin 4) : (faceTransports U p i).det = 1 := by apply _root_.YangMills.Construction.Tower.CurvatureHessianFacts.faceTransports_det <;> assumption
theorem scaledEdgeCoboundary_mem {b : Edge L n k 0 → ComplexMatrix2}
    (hb : b ∈ complexEdgeForms L n k 0) (p : Face L n k 0) :
    scaledEdgeCoboundary b p ∈ ComplexMatrix2.traceless := by
  rw [scaledEdgeCoboundary_eq_sum]
  exact ComplexMatrix2.traceless.sum_mem fun i _ =>
    coboundaryCoeff_mem _ i (hb.1 _ (faceEdge_isPositivelyOriented p i))
theorem holonomyDefect_mem {U b : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup)
    (hb : b ∈ complexEdgeForms L n k 0) (p : Face L n k 0) :
    holonomyDefect U b p ∈ ComplexMatrix2.traceless := by
  rw [holonomyDefect_eq_sum]
  exact ComplexMatrix2.traceless.sum_mem fun i _ =>
    defectCoeff_mem _ (faceTransports_det hU p) i (hb.1 _ (faceEdge_isPositivelyOriented p i))
theorem complexActionHessian_diag_eq (hplaq : FaceTermDerivatives.HoldsOnPeriodicLevel L n k 0)
    (hη : finestMesh L k ≠ 0) {U b : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup)
    (hb : b ∈ complexEdgeForms L n k 0)
    (hfin : {p : Face L n k 0 | ∃ i, b (faceEdge p i) ≠ 0}.Finite) :
    complexActionHessian U (finestMesh L k • b) (finestMesh L k • b) =
      (finestMesh L k : ℂ) ^ 4 * ∑ᶠ p, halfFaceTrace U p *
        ∑ a, pauliCoeffLinear a (scaledEdgeCoboundary b p + holonomyDefect U b p) ^ 2 +
      curvatureBilinear U b b := by
  have h := ((hplaq _ (real_smul_mem_complexEdgeForms hb (finestMesh L k))).1 U hU).2.1
  rw [← h]
  have hterm : ∀ p : Face L n k 0,
      FaceTermDerivatives.secondDerivExpr
        (transportedForm U (finestMesh L k • b) p) (PeriodicLattice.plaquetteHolonomy U p) =
      (finestMesh L k : ℂ) ^ 4 * (halfFaceTrace U p *
        ∑ a, pauliCoeffLinear a (scaledEdgeCoboundary b p + holonomyDefect U b p) ^ 2) +
      (finestMesh L k : ℂ) ^ 4 * ((Complex.I / 2) *
        ComplexMatrix2.fullTrace (bracketSumOrdered (transportedForm U b p) (transportedForm U b p) *
          curvatureMatrix U p)) := fun p => by
    rw [transportedForm_smul]
    exact secondDerivExpr_smul _ _ hη _
      (ComplexMatrix2.traceless.add_mem (scaledEdgeCoboundary_mem hb p) (holonomyDefect_mem hU hb p))
      (sum_transportedForm U b p hη)
  simp only [hterm]
  have hzero : ∀ p : Face L n k 0, p ∉ {p : Face L n k 0 |
      ∃ i, b (faceEdge p i) ≠ 0} → ∀ i, b (faceEdge p i) = 0 := fun p hp i => by
    by_contra hne
    exact hp ⟨i, hne⟩
  have hX : ∀ p : Face L n k 0, (∀ i, b (faceEdge p i) = 0) →
      scaledEdgeCoboundary b p + holonomyDefect U b p = 0 := fun p h0 => by
    rw [scaledEdgeCoboundary_eq_sum, holonomyDefect_eq_sum]
    simp [h0]
  have hY : ∀ p : Face L n k 0, (∀ i, b (faceEdge p i) = 0) →
      transportedForm U b p = 0 := fun p h0 => by
    funext i
    simp [transportedForm, h0, ComplexMatrix2.conjugateBy]
  have f₁ : (Function.support fun p : Face L n k 0 => halfFaceTrace U p *
      ∑ a, pauliCoeffLinear a (scaledEdgeCoboundary b p + holonomyDefect U b p) ^ 2).Finite := by
    refine hfin.subset fun p hp => ?_
    by_contra hno
    exact hp (by simp [hX p (hzero p hno)])
  have f₂ : (Function.support fun p : Face L n k 0 => (Complex.I / 2) *
      ComplexMatrix2.fullTrace (bracketSumOrdered (transportedForm U b p) (transportedForm U b p) *
        curvatureMatrix U p)).Finite := by
    refine hfin.subset fun p hp => ?_
    by_contra hno
    exact hp (by simp [hY p (hzero p hno), bracketSumOrdered, ComplexMatrix2.fullTrace])
  have f₁' := support_const_mul_finite ((finestMesh L k : ℂ) ^ 4) f₁
  have f₂' := support_const_mul_finite ((finestMesh L k : ℂ) ^ 4) f₂
  rw [finsum_add_distrib f₁' f₂', ← mul_finsum, ← mul_finsum]
  simp only [curvatureBilinear]
theorem finite_faces_meeting_support (hsix : FacesContainingEdge.Periodic L n k 0)
    {f : Fin 3 × PositiveEdge L n k 0 → ℂ} (hf : (Function.support f).Finite) :
    {p : Face L n k 0 | ∃ i, coeffForm f (faceEdge p i) ≠ 0}.Finite := by apply _root_.YangMills.Construction.Tower.CurvatureHessianFacts.finite_faces_touching <;> assumption
theorem fourEdgeMap_coboundary (f : Fin 3 × PositiveEdge L n k 0 → ℂ)
    (κ : Fin 3 × Face L n k 0) :
    fourEdgeMap positiveFaceEdge (fun _ i => coboundaryCoeff (finestMesh L k) i) f κ =
      pauliCoeff κ.1 (scaledEdgeCoboundary (coeffForm f) κ.2) := by
  change pauliCoeff κ.1 _ = _
  rw [scaledEdgeCoboundary_eq_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [coeffForm_apply f (faceEdge_isPositivelyOriented κ.2 i)]
    rfl
theorem fourEdgeMap_defect (U : Edge L n k 0 → ComplexMatrix2)
    (f : Fin 3 × PositiveEdge L n k 0 → ℂ) (κ : Fin 3 × Face L n k 0) :
    fourEdgeMap positiveFaceEdge
        (fun p i => defectCoeff (finestMesh L k) (faceTransports U p) i) f κ =
      pauliCoeff κ.1 (holonomyDefect U (coeffForm f) κ.2) := by
  change pauliCoeff κ.1 _ = _
  rw [holonomyDefect_eq_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [coeffForm_apply f (faceEdge_isPositivelyOriented κ.2 i)]
    rfl
theorem weightedSquareSum_eq (hL : 13 ≤ L) (hn : 0 < n) {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup)
    (f : Fin 3 × PositiveEdge L n k 0 → ℂ) :
    weightedSquareSum (halfFaceTrace U)
        (fourEdgeMap positiveFaceEdge (fun _ i => coboundaryCoeff (finestMesh L k) i) f)
        (fourEdgeMap positiveFaceEdge
          (fun p i => defectCoeff (finestMesh L k) (faceTransports U p) i) f) =
      ∑ᶠ p, halfFaceTrace U p * ∑ a, pauliCoeffLinear a
        (scaledEdgeCoboundary (coeffForm f) p + holonomyDefect U (coeffForm f) p) ^ 2 := by
  refine finsum_congr fun p => ?_
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  have m₁ := scaledEdgeCoboundary_mem (coeffForm_mem hL hn f) p
  have m₂ := holonomyDefect_mem hU (coeffForm_mem hL hn f) p
  rw [fourEdgeMap_coboundary, fourEdgeMap_defect, pauliCoeff_eq_linear m₁, pauliCoeff_eq_linear m₂,
    map_add]
theorem hessian_decomposition_at
    (hdet : ∀ Z : ComplexMatrix2,
      (ComplexMatrix2.matExp Z).det = Complex.exp (ComplexMatrix2.fullTrace Z))
    (hL : 13 ≤ L) (hn : 0 < n) (hη : finestMesh L k ≠ 0)
    (hplaq : FaceTermDerivatives.HoldsOnPeriodicLevel L n k 0)
    (hA : HessianKernel.HoldsOnTorus L n k 0)
    (hsix : FacesContainingEdge.Periodic L n k 0)
    (hF : CurvatureHessianFacts.OnPeriodicSide L n k)
    {a : Edge L n k 0 → ComplexMatrix2} (ha : a ∈ complexEdgeForms L n k 0) :
    (rescaledOperators L n k (remainderGaugeField a)).H =
      coboundarySquareKernel L n k (remainderGaugeField a) +
        curvatureKernel (remainderGaugeField a) := by
  classical
  have hU := remainderGaugeField_mem hdet hL hn ha
  set U := remainderGaugeField a with hUdef
  obtain ⟨T₁, hT₁, hs₁⟩ := exists_represents_fourEdgeMap (positiveFaceEdge (L := L) (n := n) (k := k))
    (fun _ i => coboundaryCoeff (finestMesh L k) i) (fun _ i _ h => coboundaryCoeff_mem _ i h)
  obtain ⟨T₂, hT₂, hs₂⟩ := exists_represents_fourEdgeMap (positiveFaceEdge (L := L) (n := n) (k := k))
    (fun p i => defectCoeff (finestMesh L k) (faceTransports U p) i)
    (fun p i _ h => defectCoeff_mem _ (faceTransports_det hU p) i h)
  have e₁ : scaledEdgeCoboundaryKernel L n k 0 = T₁ := by
    have hm : PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L n k 0)
        (vertexCoordinate (Face L n k 0)) scaledEdgeCoboundary =
        fourEdgeMap positiveFaceEdge (fun _ i => coboundaryCoeff (finestMesh L k) i) := by
      funext f κ
      exact (fourEdgeMap_coboundary f κ).symm
    change kernelOfMap (PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L n k 0)
      (vertexCoordinate (Face L n k 0)) scaledEdgeCoboundary) = T₁
    rw [hm]
    exact kernelOfMap_eq hT₁
  have e₂ : holonomyDefectKernel L n k U = T₂ := by
    have hm : PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L n k 0)
        (vertexCoordinate (Face L n k 0)) (holonomyDefect U) =
        fourEdgeMap positiveFaceEdge
          (fun p i => defectCoeff (finestMesh L k) (faceTransports U p) i) := by
      funext f κ
      exact (fourEdgeMap_defect U f κ).symm
    change kernelOfMap (PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L n k 0)
      (vertexCoordinate (Face L n k 0)) (holonomyDefect U)) = T₂
    rw [hm]
    exact kernelOfMap_eq hT₂
  have eZ : halfFaceTraceKernel L n k U =
      fun κ κ' => open Classical in if κ' = κ then halfFaceTrace U κ.2 else 0 := by
    have hm : PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (Face L n k 0))
        (vertexCoordinate (Face L n k 0)) (halfFaceTraceMul U) =
        pointwiseMul (halfFaceTrace U) := rfl
    change kernelOfMap (PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (Face L n k 0))
      (vertexCoordinate (Face L n k 0)) (halfFaceTraceMul U)) = _
    rw [hm]
    exact kernelOfMap_eq (represents_pointwiseMul _)
  have hspec := (hF.1 U).2.1
  have hsymF : ∀ ι ι', curvatureKernel U ι ι' = curvatureKernel U ι' ι := fun ι ι' => by
    conv_lhs => rw [← show meshTranspose (finestMesh L k) (finestMesh L k)
      (curvatureKernel U) = curvatureKernel U from hspec.1]
    exact meshTranspose_apply hη _ ι ι'
  have hηc : (finestMesh L k : ℂ) ≠ 0 := by exact_mod_cast hη
  have h4 : (finestMesh L k : ℂ) ^ 4 ≠ 0 := pow_ne_zero _ hηc
  have hHe : ∀ ι ι', (rescaledOperators L n k U).H ι ι' = ((finestMesh L k : ℂ) ^ 4)⁻¹ *
      complexActionHessian U (finestMesh L k • coeffForm (unitVec ι))
        (finestMesh L k • coeffForm (unitVec ι')) := fun ι ι' => by
    rw [← basisForm_eq_coeffForm, ← basisForm_eq_coeffForm]
    change (((finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) * _ = _
    push_cast
    rfl
  unfold coboundarySquareKernel coboundaryAddDefectKernel
  rw [e₁, e₂]
  refine kernel_eq_of_quadratic (finestMesh L k) hη positiveFaceEdge
    (fun s => ((hsix.2.2 {s} (finite_singleton s)).subset ?_)) hT₁ hT₂ hs₁ hs₂
    (halfFaceTrace U) (fun κ κ' => by rw [eZ]) _ _ (fun ι => ?_) (fun ι ι' => ?_)
  · rintro p ⟨i, rfl⟩
    exact ⟨_, rfl, faceEdge_mem_faceEdges p i⟩
  · have hstar := complexActionHessian_diag_eq hplaq hη hU (coeffForm_mem hL hn (unitVec ι))
      (finite_faces_meeting_support hsix (basisFunction ι).2)
    have hform := hspec.2 (basisFunction ι)
    rw [kernelPairing_unitVec] at hform
    rw [hHe, hstar, weightedSquareSum_eq hL hn hU]
    change _ * (_ + curvatureBilinear U (coeffForm (unitVec ι)) (coeffForm (unitVec ι))) = _
    rw [show curvatureBilinear U (coeffForm (unitVec ι)) (coeffForm (unitVec ι)) = _ from hform.symm]
    simp only [meshWeight]
    push_cast
    field_simp
  · have hbil := (hA U hU).1
    let B := finestMesh L k • coeffForm (unitVec ι)
    let B' := finestMesh L k • coeffForm (unitVec ι')
    have mB : B ∈ (complexEdgeForms L n k 0 : Set (Edge L n k 0 → ComplexMatrix2)) :=
      real_smul_mem_complexEdgeForms (coeffForm_mem hL hn _) _
    have mB' : B' ∈ (complexEdgeForms L n k 0 : Set (Edge L n k 0 → ComplexMatrix2)) :=
      real_smul_mem_complexEdgeForms (coeffForm_mem hL hn _) _
    have mS : B + B' ∈ (complexEdgeForms L n k 0 : Set (Edge L n k 0 → ComplexMatrix2)) :=
      Submodule.add_mem _ mB mB'
    have b₁ := (hbil 1 B mB B' mB' (B + B') mS).1
    have b₂ := (hbil 1 B mB B' mB' B mB).2.1
    have b₃ := (hbil 1 B mB B' mB' B' mB').2.1
    have b₄ := (hbil 0 B' mB' B' mB' B mB).2.2
    simp only [one_smul, one_mul] at b₁ b₂ b₃ b₄
    have hsum : finestMesh L k • coeffForm (unitVec ι + unitVec ι') = B + B' := by
      rw [coeffForm_add, smul_add]
    have hstar := complexActionHessian_diag_eq hplaq hη hU
      (coeffForm_mem hL hn (unitVec ι + unitVec ι'))
      (finite_faces_meeting_support hsix (basisFunction ι + basisFunction ι').2)
    have hform := hspec.2 (basisFunction ι + basisFunction ι')
    have hform' : (((finestMesh L k ^ 4 : ℝ)) : ℂ) * (curvatureKernel U ι ι +
        curvatureKernel U ι' ι' + 2 * curvatureKernel U ι ι') =
        curvatureBilinear U (coeffForm (unitVec ι + unitVec ι'))
          (coeffForm (unitVec ι + unitVec ι')) := by
      rw [← kernelPairing_unitVec_add _ _ hsymF]
      exact hform
    rw [hsum, b₁, b₂, b₃, ← hform'] at hstar
    rw [hHe, hHe, hHe, weightedSquareSum_eq hL hn hU]
    push_cast at hstar
    exact polarization_step h4 hstar b₄
end FiniteSide
end YangMills.Construction.Tower.WilsonHessianProof
namespace YangMills.Construction.Tower.FullSpace.WilsonHessianProof
open YangMills.Construction.Tower.WilsonHessianProof
section Infinite
variable {L k : ℕ}
theorem forwardFrom_isPositivelyOriented (x : Vertex L k 0) (μ : Fin 4) :
    (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem faceEdge_isPositivelyOriented (p : Face L k 0) (i : Fin 4) :
    (faceEdge p i).IsPositivelyOriented := by
  fin_cases i <;> exact forwardFrom_isPositivelyOriented _ _
def positiveFaceEdge (p : Face L k 0) (i : Fin 4) : PositiveEdge (meshAt L k 0) :=
  ⟨faceEdge p i, faceEdge_isPositivelyOriented p i⟩
theorem faceEdge_mem_faceEdges (p : Face L k 0) (i : Fin 4) :
    faceEdge p i ∈ faceEdges p :=
  List.getElem_mem _
theorem not_isPositivelyOriented_opposite (hpos : 0 < meshAt L k 0) {b : Edge L k 0}
    (h : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := h
  rintro ⟨ν, hν⟩
  have hν' : b.initial - b.terminal = InfiniteLattice.axisStep (meshAt L k 0) ν := hν
  have hsum : InfiniteLattice.axisStep (meshAt L k 0) μ +
      InfiniteLattice.axisStep (meshAt L k 0) ν = 0 := by
    rw [← hμ, ← hν']
    abel
  have hc := congrFun (congrArg Subtype.val hsum) μ
  have hstep : ∀ κ, ((InfiniteLattice.axisStep (meshAt L k 0) κ :
      InfiniteLattice.LatticePoint (meshAt L k 0)) : InfiniteLattice.AmbientSpace) μ =
        if μ = κ then meshAt L k 0 else 0 := fun κ => by
    by_cases e : μ = κ
    · subst e
      simp [InfiniteLattice.axisStep]
    · simp [InfiniteLattice.axisStep, e]
  have hc' : ((InfiniteLattice.axisStep (meshAt L k 0) μ :
      InfiniteLattice.LatticePoint (meshAt L k 0)) : InfiniteLattice.AmbientSpace) μ +
      ((InfiniteLattice.axisStep (meshAt L k 0) ν :
      InfiniteLattice.LatticePoint (meshAt L k 0)) : InfiniteLattice.AmbientSpace) μ = 0 := hc
  rw [hstep, hstep] at hc'
  by_cases e : μ = ν
  · simp only [e, if_true] at hc'
    linarith
  · simp only [e, if_false, if_true, add_zero] at hc'
    linarith
theorem opposite_isPositivelyOriented_of_not {b : Edge L k 0} (h : ¬b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, e | e⟩ := b.isAdjacent
  · exact absurd ⟨μ, e⟩ h
  · refine ⟨μ, ?_⟩
    change b.initial - b.terminal = _
    rw [← neg_sub, e, neg_neg]
abbrev coeffForm (f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) : Edge L k 0 → ComplexMatrix2 :=
  (edgePauliCoordinates L k 0).ofCoeffs f
theorem coeffForm_apply (f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) {b : Edge L k 0}
    (h : b.IsPositivelyOriented) : coeffForm f b = ofPauliCoeffs f ⟨b, h⟩ := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureHessianAtInfinity.edgeField_apply <;> assumption
theorem coeffForm_mem (hpos : 0 < meshAt L k 0) (f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) :
    coeffForm f ∈ complexEdgeForms (meshAt L k 0) := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [coeffForm_apply f hb]
    exact ofPauliCoeffs_mem_traceless _ _
  · by_cases hb : b.IsPositivelyOriented
    · have hr := not_isPositivelyOriented_opposite hpos hb
      rw [coeffForm_apply f hb]
      have hb' : b.opposite.opposite.IsPositivelyOriented := hb
      simp only [coeffForm, edgePauliCoordinates, extendOddly, if_neg hr, dif_pos hb']
      rfl
    · have hr := opposite_isPositivelyOriented_of_not hb
      rw [coeffForm_apply f hr]
      simp [coeffForm, edgePauliCoordinates, extendOddly, hb, hr]
theorem basisForm_eq_coeffForm (ι : Fin 3 × PositiveEdge (meshAt L k 0)) :
    basisForm ι.1 ι.2 = coeffForm (unitVec ι) := by
  classical
  simp only [basisForm, coeffForm, edgePauliCoordinates]
  congr 1
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [dif_pos hb]
    simp only [ofPauliCoeffs]
    by_cases e : b = ι.2.1
    · rw [if_pos e]
      rw [Finset.sum_eq_single ι.1]
      · have : (ι.1, (⟨b, hb⟩ : PositiveEdge (meshAt L k 0))) = ι :=
          Prod.ext rfl (Subtype.ext e)
        rw [this, unitVec_self, one_smul]
      · intro a _ ha
        have : (a, (⟨b, hb⟩ : PositiveEdge (meshAt L k 0))) ≠ ι := fun h =>
          ha (congrArg Prod.fst h)
        rw [unitVec_of_ne this, zero_smul]
      · simp
    · rw [if_neg e]
      symm
      refine Finset.sum_eq_zero fun a _ => ?_
      have : (a, (⟨b, hb⟩ : PositiveEdge (meshAt L k 0))) ≠ ι := fun h =>
        e (congrArg Subtype.val (congrArg Prod.snd h))
      rw [unitVec_of_ne this, zero_smul]
  · rw [dif_neg hb, if_neg]
    intro e
    exact hb (e ▸ ι.2.2)
theorem coeffForm_add (f g : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) :
    coeffForm (f + g) = coeffForm f + coeffForm g := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [Pi.add_apply, coeffForm_apply _ hb, ofPauliCoeffs, add_smul, Finset.sum_add_distrib]
  · have hr := opposite_isPositivelyOriented_of_not hb
    simp only [coeffForm, edgePauliCoordinates, extendOddly, Pi.add_apply, if_neg hb, dif_pos hr,
      ofPauliCoeffs, add_smul, Finset.sum_add_distrib, neg_add]
theorem scaledEdgeCoboundary_eq_sum (b : Edge L k 0 → ComplexMatrix2) (p : Face L k 0) :
    scaledEdgeCoboundary b p =
      ∑ i, coboundaryCoeff (finestMesh L k) i (b (faceEdge p i)) := by
  simp only [scaledEdgeCoboundary, Pi.smul_apply, edgeCoboundary, coboundaryCoeff,
    LinearMap.smul_apply, LinearMap.id_apply, Fin.sum_univ_four, transportSign,
    real_smul_eq_complex_smul]
  simp only [faceEdge, faceEdges, finestMesh]
  simp [smul_add, mul_neg, neg_smul, sub_eq_add_neg, add_assoc, Complex.ofReal_inv]
theorem holonomyDefect_eq_sum (U b : Edge L k 0 → ComplexMatrix2) (p : Face L k 0) :
    holonomyDefect U b p =
      ∑ i, defectCoeff (finestMesh L k) (faceTransports U p) i (b (faceEdge p i)) := by
  simp only [holonomyDefect, defectCoeff, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, conjugateLinear_apply, real_smul_eq_complex_smul, Finset.smul_sum,
    smul_smul, Complex.ofReal_inv]
theorem sum_transportedForm (U b : Edge L k 0 → ComplexMatrix2) (p : Face L k 0)
    (hη : finestMesh L k ≠ 0) :
    ∑ i, transportedForm U b p i =
      finestMesh L k • (scaledEdgeCoboundary b p + holonomyDefect U b p) := by
  have hηc : (finestMesh L k : ℂ) ≠ 0 := by exact_mod_cast hη
  rw [scaledEdgeCoboundary_eq_sum, holonomyDefect_eq_sum, ← Finset.sum_add_distrib,
    real_smul_eq_complex_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [transportedForm, coboundaryCoeff, defectCoeff, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.id_apply, conjugateLinear_apply, ← smul_add, add_sub_cancel,
    smul_smul]
  rw [← mul_assoc, mul_inv_cancel₀ hηc, one_mul]
end Infinite
section Infinite
variable {L k : ℕ}
theorem real_smul_mem_complexEdgeForms {b : Edge L k 0 → ComplexMatrix2}
    (hb : b ∈ complexEdgeForms (meshAt L k 0)) (c : ℝ) :
    c • b ∈ complexEdgeForms (meshAt L k 0) := by
  have e : c • b = (c : ℂ) • b := by
    funext x
    exact real_smul_eq_complex_smul _ _
  rw [e]
  exact Submodule.smul_mem _ _ hb
theorem transportedForm_smul (U b : Edge L k 0 → ComplexMatrix2) (c : ℝ) (p : Face L k 0) :
    transportedForm U (c • b) p = fun i => c • transportedForm U b p i := by
  funext i
  simp only [transportedForm, Pi.smul_apply, ComplexMatrix2.conjugateBy, real_smul_eq_complex_smul,
    mul_smul_comm, smul_mul_assoc]
  rw [smul_comm]
theorem remainderGaugeField_mem
    (hdet : ∀ Z : ComplexMatrix2,
      (ComplexMatrix2.matExp Z).det = Complex.exp (ComplexMatrix2.fullTrace Z))
    (hpos : 0 < meshAt L k 0) {a : Edge L k 0 → ComplexMatrix2}
    (ha : a ∈ complexEdgeForms (meshAt L k 0)) :
    remainderGaugeField a ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup := by
  have hA := real_smul_mem_complexEdgeForms ha (finestMesh L k)
  have hvp : ∀ b : Edge L k 0, b.IsPositivelyOriented →
      remainderGaugeField a b =
        ComplexMatrix2.matExp (Complex.I • (finestMesh L k • a) b) := fun b hb => by
    simp [remainderGaugeField, scaledRemainderForm,
      expForm, expTwist, hb]
  have hneg : ∀ b : Edge L k 0, ¬b.IsPositivelyOriented →
      remainderGaugeField a b =
        (ComplexMatrix2.matExp (Complex.I • (finestMesh L k • a) b.opposite))⁻¹ := fun b hb => by
    simp [remainderGaugeField, scaledRemainderForm,
      expForm, expTwist, hb]
  have hd : ∀ b : Edge L k 0, b.IsPositivelyOriented →
      (ComplexMatrix2.matExp (Complex.I • (finestMesh L k • a) b)).det = 1 := fun b hb => by
    have ht : Matrix.trace ((finestMesh L k • a) b) = 0 := hA.1 b hb
    rw [hdet]
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul, ht, smul_zero, Complex.exp_zero]
  have hu : ∀ b : Edge L k 0, b.IsPositivelyOriented →
      IsUnit (ComplexMatrix2.matExp (Complex.I • (finestMesh L k • a) b)).det := fun b hb => by
    rw [hd b hb]
    exact isUnit_one
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [hvp b hb]
      exact hd b hb
    · rw [hneg b hb]
      change Matrix.det _ = 1
      rw [Matrix.det_nonsing_inv, hd _ (opposite_isPositivelyOriented_of_not hb)]
      simp
  · by_cases hb : b.IsPositivelyOriented
    · rw [hvp b hb, hneg _ (not_isPositivelyOriented_opposite hpos hb)]
      rfl
    · rw [hneg b hb, hvp _ (opposite_isPositivelyOriented_of_not hb),
        Matrix.nonsing_inv_nonsing_inv _ (hu _ (opposite_isPositivelyOriented_of_not hb))]
theorem faceTransports_det {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup) (p : Face L k 0)
    (i : Fin 4) : (faceTransports U p i).det = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureHessianAtInfinity.faceTransports_det <;> assumption
theorem scaledEdgeCoboundary_mem {b : Edge L k 0 → ComplexMatrix2}
    (hb : b ∈ complexEdgeForms (meshAt L k 0)) (p : Face L k 0) :
    scaledEdgeCoboundary b p ∈ ComplexMatrix2.traceless := by
  rw [scaledEdgeCoboundary_eq_sum]
  exact ComplexMatrix2.traceless.sum_mem fun i _ =>
    coboundaryCoeff_mem _ i (hb.1 _ (faceEdge_isPositivelyOriented p i))
theorem holonomyDefect_mem {U b : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (hb : b ∈ complexEdgeForms (meshAt L k 0)) (p : Face L k 0) :
    holonomyDefect U b p ∈ ComplexMatrix2.traceless := by
  rw [holonomyDefect_eq_sum]
  exact ComplexMatrix2.traceless.sum_mem fun i _ =>
    defectCoeff_mem _ (faceTransports_det hU p) i (hb.1 _ (faceEdge_isPositivelyOriented p i))
theorem complexActionHessian_diag_eq (hplaq : FaceTermDerivatives.HoldsOnFullSpaceLevel L k 0)
    (hη : finestMesh L k ≠ 0) {U b : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (hb : b ∈ complexEdgeForms (meshAt L k 0))
    (hfs : HasFiniteEdgeSupport (finestMesh L k • b))
    (hfin : {p : Face L k 0 | ∃ i, b (faceEdge p i) ≠ 0}.Finite) :
    complexActionHessian U (finestMesh L k • b) (finestMesh L k • b) =
      (finestMesh L k : ℂ) ^ 4 * ∑ᶠ p, halfFaceTrace U p *
        ∑ a, pauliCoeffLinear a (scaledEdgeCoboundary b p + holonomyDefect U b p) ^ 2 +
      curvatureBilinear U b b := by
  have h := (((hplaq _ (real_smul_mem_complexEdgeForms hb (finestMesh L k))).2 hfs).1 U hU).1
  rw [← h]
  have hterm : ∀ p : Face L k 0,
      FaceTermDerivatives.secondDerivExpr
        (transportedForm U (finestMesh L k • b) p) (faceVariable U p) =
      (finestMesh L k : ℂ) ^ 4 * (halfFaceTrace U p *
        ∑ a, pauliCoeffLinear a (scaledEdgeCoboundary b p + holonomyDefect U b p) ^ 2) +
      (finestMesh L k : ℂ) ^ 4 * ((Complex.I / 2) *
        ComplexMatrix2.fullTrace (bracketSumOrdered (transportedForm U b p) (transportedForm U b p) *
          curvatureMatrix U p)) := fun p => by
    rw [transportedForm_smul]
    exact secondDerivExpr_smul _ _ hη _
      (ComplexMatrix2.traceless.add_mem (scaledEdgeCoboundary_mem hb p) (holonomyDefect_mem hU hb p))
      (sum_transportedForm U b p hη)
  simp only [hterm]
  have hzero : ∀ p : Face L k 0, p ∉ {p : Face L k 0 |
      ∃ i, b (faceEdge p i) ≠ 0} → ∀ i, b (faceEdge p i) = 0 := fun p hp i => by
    by_contra hne
    exact hp ⟨i, hne⟩
  have hX : ∀ p : Face L k 0, (∀ i, b (faceEdge p i) = 0) →
      scaledEdgeCoboundary b p + holonomyDefect U b p = 0 := fun p h0 => by
    rw [scaledEdgeCoboundary_eq_sum, holonomyDefect_eq_sum]
    simp [h0]
  have hY : ∀ p : Face L k 0, (∀ i, b (faceEdge p i) = 0) →
      transportedForm U b p = 0 := fun p h0 => by
    funext i
    simp [transportedForm, h0, ComplexMatrix2.conjugateBy]
  have f₁ : (Function.support fun p : Face L k 0 => halfFaceTrace U p *
      ∑ a, pauliCoeffLinear a (scaledEdgeCoboundary b p + holonomyDefect U b p) ^ 2).Finite := by
    refine hfin.subset fun p hp => ?_
    by_contra hno
    exact hp (by simp [hX p (hzero p hno)])
  have f₂ : (Function.support fun p : Face L k 0 => (Complex.I / 2) *
      ComplexMatrix2.fullTrace (bracketSumOrdered (transportedForm U b p) (transportedForm U b p) *
        curvatureMatrix U p)).Finite := by
    refine hfin.subset fun p hp => ?_
    by_contra hno
    exact hp (by simp [hY p (hzero p hno), bracketSumOrdered, ComplexMatrix2.fullTrace])
  have f₁' := support_const_mul_finite ((finestMesh L k : ℂ) ^ 4) f₁
  have f₂' := support_const_mul_finite ((finestMesh L k : ℂ) ^ 4) f₂
  rw [finsum_add_distrib f₁' f₂', ← mul_finsum, ← mul_finsum]
  simp only [curvatureBilinear]
theorem finite_faces_meeting_support (hsix : FacesContainingEdge.OnFullSpace L k 0)
    {f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ} (hf : (Function.support f).Finite) :
    {p : Face L k 0 | ∃ i, coeffForm f (faceEdge p i) ≠ 0}.Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureHessianAtInfinity.finite_faces_touching <;> assumption
theorem smul_coeffForm_hasFiniteEdgeSupport {f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ}
    (hf : (Function.support f).Finite) (c : ℝ) : HasFiniteEdgeSupport (c • coeffForm f) := by
  refine ((hf.image Prod.snd).image Subtype.val).subset ?_
  rintro b ⟨hb, hne⟩
  have hne' : coeffForm f b ≠ 0 := fun h0 => hne (by simp [h0])
  rw [coeffForm_apply f hb] at hne'
  have : ∃ a, f (a, ⟨b, hb⟩) ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hne' (Finset.sum_eq_zero fun a _ => by rw [hno a, zero_smul])
  obtain ⟨a, ha⟩ := this
  exact ⟨⟨b, hb⟩, ⟨_, ha, rfl⟩, rfl⟩
theorem fourEdgeMap_coboundary (f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ)
    (κ : Fin 3 × Face L k 0) :
    fourEdgeMap positiveFaceEdge (fun _ i => coboundaryCoeff (finestMesh L k) i) f κ =
      pauliCoeff κ.1 (scaledEdgeCoboundary (coeffForm f) κ.2) := by
  change pauliCoeff κ.1 _ = _
  rw [scaledEdgeCoboundary_eq_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [coeffForm_apply f (faceEdge_isPositivelyOriented κ.2 i)]
    rfl
theorem fourEdgeMap_defect (U : Edge L k 0 → ComplexMatrix2)
    (f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) (κ : Fin 3 × Face L k 0) :
    fourEdgeMap positiveFaceEdge
        (fun p i => defectCoeff (finestMesh L k) (faceTransports U p) i) f κ =
      pauliCoeff κ.1 (holonomyDefect U (coeffForm f) κ.2) := by
  change pauliCoeff κ.1 _ = _
  rw [holonomyDefect_eq_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [coeffForm_apply f (faceEdge_isPositivelyOriented κ.2 i)]
    rfl
theorem weightedSquareSum_eq (hpos : 0 < meshAt L k 0) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) :
    weightedSquareSum (halfFaceTrace U)
        (fourEdgeMap positiveFaceEdge (fun _ i => coboundaryCoeff (finestMesh L k) i) f)
        (fourEdgeMap positiveFaceEdge
          (fun p i => defectCoeff (finestMesh L k) (faceTransports U p) i) f) =
      ∑ᶠ p, halfFaceTrace U p * ∑ a, pauliCoeffLinear a
        (scaledEdgeCoboundary (coeffForm f) p + holonomyDefect U (coeffForm f) p) ^ 2 := by
  refine finsum_congr fun p => ?_
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  have m₁ := scaledEdgeCoboundary_mem (coeffForm_mem hpos f) p
  have m₂ := holonomyDefect_mem hU (coeffForm_mem hpos f) p
  rw [fourEdgeMap_coboundary, fourEdgeMap_defect, pauliCoeff_eq_linear m₁, pauliCoeff_eq_linear m₂,
    map_add]
theorem hessian_decomposition_at
    (hdet : ∀ Z : ComplexMatrix2,
      (ComplexMatrix2.matExp Z).det = Complex.exp (ComplexMatrix2.fullTrace Z))
    (hpos : 0 < meshAt L k 0) (hη : finestMesh L k ≠ 0)
    (hplaq : FaceTermDerivatives.HoldsOnFullSpaceLevel L k 0)
    (hA : HessianKernel.HoldsOnFullSpace L k 0)
    (hsix : FacesContainingEdge.OnFullSpace L k 0)
    (hF : CurvatureHessianFacts.OnFullSpace L k)
    {a : Edge L k 0 → ComplexMatrix2} (ha : a ∈ complexEdgeForms (meshAt L k 0)) :
    (rescaledOperators L k (remainderGaugeField a)).H =
      coboundarySquareKernel L k (remainderGaugeField a) +
        curvatureKernel (remainderGaugeField a) := by
  classical
  have hU := remainderGaugeField_mem hdet hpos ha
  set U := remainderGaugeField a with hUdef
  obtain ⟨T₁, hT₁, hs₁⟩ := exists_represents_fourEdgeMap (positiveFaceEdge (L := L) (k := k))
    (fun _ i => coboundaryCoeff (finestMesh L k) i) (fun _ i _ h => coboundaryCoeff_mem _ i h)
  obtain ⟨T₂, hT₂, hs₂⟩ := exists_represents_fourEdgeMap (positiveFaceEdge (L := L) (k := k))
    (fun p i => defectCoeff (finestMesh L k) (faceTransports U p) i)
    (fun p i _ h => defectCoeff_mem _ (faceTransports_det hU p) i h)
  have e₁ : scaledEdgeCoboundaryKernel L k 0 = T₁ := by
    have hm : PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L k 0)
        (vertexCoordinate (Face L k 0)) scaledEdgeCoboundary =
        fourEdgeMap positiveFaceEdge (fun _ i => coboundaryCoeff (finestMesh L k) i) := by
      funext f κ
      exact (fourEdgeMap_coboundary f κ).symm
    change kernelOfMap (PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L k 0)
      (vertexCoordinate (Face L k 0)) scaledEdgeCoboundary) = T₁
    rw [hm]
    exact kernelOfMap_eq hT₁
  have e₂ : holonomyDefectKernel L k U = T₂ := by
    have hm : PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L k 0)
        (vertexCoordinate (Face L k 0)) (holonomyDefect U) =
        fourEdgeMap positiveFaceEdge
          (fun p i => defectCoeff (finestMesh L k) (faceTransports U p) i) := by
      funext f κ
      exact (fourEdgeMap_defect U f κ).symm
    change kernelOfMap (PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L k 0)
      (vertexCoordinate (Face L k 0)) (holonomyDefect U)) = T₂
    rw [hm]
    exact kernelOfMap_eq hT₂
  have eZ : halfFaceTraceKernel L k U =
      fun κ κ' => open Classical in if κ' = κ then halfFaceTrace U κ.2 else 0 := by
    have hm : PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (Face L k 0))
        (vertexCoordinate (Face L k 0)) (halfFaceTraceMul U) =
        pointwiseMul (halfFaceTrace U) := rfl
    change kernelOfMap (PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (Face L k 0))
      (vertexCoordinate (Face L k 0)) (halfFaceTraceMul U)) = _
    rw [hm]
    exact kernelOfMap_eq (represents_pointwiseMul _)
  have hspec := (hF.1 U).2.1
  have hsymF : ∀ ι ι', curvatureKernel U ι ι' = curvatureKernel U ι' ι := fun ι ι' => by
    conv_lhs => rw [← show meshTranspose (finestMesh L k) (finestMesh L k)
      (curvatureKernel U) = curvatureKernel U from hspec.1]
    exact meshTranspose_apply hη _ ι ι'
  have hηc : (finestMesh L k : ℂ) ≠ 0 := by exact_mod_cast hη
  have h4 : (finestMesh L k : ℂ) ^ 4 ≠ 0 := pow_ne_zero _ hηc
  have hHe : ∀ ι ι', (rescaledOperators L k U).H ι ι' = ((finestMesh L k : ℂ) ^ 4)⁻¹ *
      complexActionHessian U (finestMesh L k • coeffForm (unitVec ι))
        (finestMesh L k • coeffForm (unitVec ι')) := fun ι ι' => by
    rw [← basisForm_eq_coeffForm, ← basisForm_eq_coeffForm]
    change (((finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) * _ = _
    push_cast
    rfl
  unfold coboundarySquareKernel coboundaryAddDefectKernel
  rw [e₁, e₂]
  refine kernel_eq_of_quadratic (finestMesh L k) hη positiveFaceEdge
    (fun s => ((hsix.2.2 {s} (finite_singleton s)).subset ?_)) hT₁ hT₂ hs₁ hs₂
    (halfFaceTrace U) (fun κ κ' => by rw [eZ]) _ _ (fun ι => ?_) (fun ι ι' => ?_)
  · rintro p ⟨i, rfl⟩
    exact ⟨_, rfl, faceEdge_mem_faceEdges p i⟩
  · have hstar := complexActionHessian_diag_eq hplaq hη hU (coeffForm_mem hpos (unitVec ι))
      (smul_coeffForm_hasFiniteEdgeSupport (basisFunction ι).2 _)
      (finite_faces_meeting_support hsix (basisFunction ι).2)
    have hform := hspec.2 (basisFunction ι)
    rw [kernelPairing_unitVec] at hform
    rw [hHe, hstar, weightedSquareSum_eq hpos hU]
    change _ * (_ + curvatureBilinear U (coeffForm (unitVec ι)) (coeffForm (unitVec ι))) = _
    rw [show curvatureBilinear U (coeffForm (unitVec ι)) (coeffForm (unitVec ι)) = _ from hform.symm]
    simp only [meshWeight]
    push_cast
    field_simp
  · have hbil := (hA U hU).1
    let B := finestMesh L k • coeffForm (unitVec ι)
    let B' := finestMesh L k • coeffForm (unitVec ι')
    have hsum : finestMesh L k • coeffForm (unitVec ι + unitVec ι') = B + B' := by
      rw [coeffForm_add, smul_add]
    have mB : B ∈ HessianKernel.finiteSupportComplexForms L k 0 :=
      ⟨real_smul_mem_complexEdgeForms (coeffForm_mem hpos _) _,
        smul_coeffForm_hasFiniteEdgeSupport (basisFunction ι).2 _⟩
    have mB' : B' ∈ HessianKernel.finiteSupportComplexForms L k 0 :=
      ⟨real_smul_mem_complexEdgeForms (coeffForm_mem hpos _) _,
        smul_coeffForm_hasFiniteEdgeSupport (basisFunction ι').2 _⟩
    have mS : B + B' ∈ HessianKernel.finiteSupportComplexForms L k 0 := by
      rw [← hsum]
      exact ⟨real_smul_mem_complexEdgeForms (coeffForm_mem hpos _) _,
        smul_coeffForm_hasFiniteEdgeSupport (basisFunction ι + basisFunction ι').2 _⟩
    have b₁ := (hbil 1 B mB B' mB' (B + B') mS).1
    have b₂ := (hbil 1 B mB B' mB' B mB).2.1
    have b₃ := (hbil 1 B mB B' mB' B' mB').2.1
    have b₄ := (hbil 0 B' mB' B' mB' B mB).2.2
    simp only [one_smul, one_mul] at b₁ b₂ b₃ b₄
    have hstar := complexActionHessian_diag_eq hplaq hη hU
      (coeffForm_mem hpos (unitVec ι + unitVec ι'))
      (smul_coeffForm_hasFiniteEdgeSupport (basisFunction ι + basisFunction ι').2 _)
      (finite_faces_meeting_support hsix (basisFunction ι + basisFunction ι').2)
    have hform := hspec.2 (basisFunction ι + basisFunction ι')
    have hform' : (((finestMesh L k ^ 4 : ℝ)) : ℂ) * (curvatureKernel U ι ι +
        curvatureKernel U ι' ι' + 2 * curvatureKernel U ι ι') =
        curvatureBilinear U (coeffForm (unitVec ι + unitVec ι'))
          (coeffForm (unitVec ι + unitVec ι')) := by
      rw [← kernelPairing_unitVec_add _ _ hsymF]
      exact hform
    rw [hsum, b₁, b₂, b₃, ← hform'] at hstar
    rw [hHe, hHe, hHe, weightedSquareSum_eq hpos hU]
    push_cast at hstar
    exact polarization_step h4 hstar b₄
end Infinite
end YangMills.Construction.Tower.FullSpace.WilsonHessianProof
namespace YangMills.Construction.Tower.WilsonHessianProof
theorem decomposition_holds (h₁ : FaceTermDerivatives.Statement)
    (h₂ : HessianKernel.KernelProperties) (h₃ : FacesContainingEdge.Holds)
    (h₄ : CurvatureHessianFacts.Claim)
    (h₅ : ComplexMatrix2.ExpLogEstimates) : WilsonHessian.DecompositionHolds := by
  intro L hL k hk
  have hL13 : 13 ≤ L := hL.2
  have hpos : 0 < meshAt L k 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    exact zpow_pos this _
  have hη : finestMesh L k ≠ 0 := hpos.ne'
  have hdet : ∀ Z : ComplexMatrix2,
      (ComplexMatrix2.matExp Z).det = Complex.exp (ComplexMatrix2.fullTrace Z) :=
    h₅.2.2.2.2.2.1
  have p₁ := h₁ L hL k 0 (Nat.zero_le _)
  have p₂ := h₂ L hL k 0 (Nat.zero_le _)
  have p₃ := h₃ L hL k 0 (Nat.zero_le _)
  have p₄ := h₄ L hL k hk
  refine ⟨fun n hn a ha => ?_, fun a ha => ?_⟩
  · exact hessian_decomposition_at hdet hL13 hn hη (p₁.1 n hn) (p₂.1 n hn) (p₃.1 n hn)
      (p₄.1 n hn) ha
  · exact FullSpace.WilsonHessianProof.hessian_decomposition_at hdet hpos hη p₁.2 p₂.2 p₃.2
      p₄.2 ha
end YangMills.Construction.Tower.WilsonHessianProof
end
