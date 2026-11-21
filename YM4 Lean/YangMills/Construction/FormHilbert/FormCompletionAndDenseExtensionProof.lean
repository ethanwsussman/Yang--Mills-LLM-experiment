import YangMills.Construction.FormHilbert.FormCompletionAndDenseExtension
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.FormHilbert
open YangMills.Construction.HilbertSpace
namespace DenseExtension
theorem forall_of_dense_of_isClosed {X : Type*} [TopologicalSpace X] {S : Set X} (hS : Dense S)
    {p : X → Prop} (hc : IsClosed {x | p x}) (h : ∀ x ∈ S, p x) (x : X) : p x :=
  closure_minimal (s := S) (t := {x | p x}) h hc (hS x)
section Forms
variable {𝔛 : Type*} [AddCommGroup 𝔛] [Module ℂ 𝔛]
theorem norm_formClass_sq {b : SesqForm 𝔛} (h : IsPosSesqForm b) (F : 𝔛) :
    ‖formClass b F‖ ^ 2 = (b F F).re := by
  have h₁ := inner_formClass h F F
  rw [inner_self_eq_norm_sq_to_K] at h₁
  have h₂ := congrArg Complex.re h₁
  rw [← h₂]
  norm_cast
theorem sesqFormCauchySchwarz_of_isPos {b : SesqForm 𝔛} (h : IsPosSesqForm b) :
    SesqFormCauchySchwarz b := by
  refine ⟨h.isConjSymm, fun F F' => ?_, ?_⟩
  · rw [← inner_formClass h F F', ← norm_formClass_sq h F, ← norm_formClass_sq h F', ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  · refine ⟨(normSeminorm ℂ (FormCompletion b)).comp (formClass b), fun F => ?_⟩
    rw [SesqForm.diagSqrt, ← norm_formClass_sq h F, Real.sqrt_sq (norm_nonneg _)]
    rfl
theorem dense_range_formClass (b : SesqForm 𝔛) :
    Dense (LinearMap.range (formClass b) : Set (FormCompletion b)) := by
  rw [LinearMap.coe_range]
  exact show DenseRange ((↑) : FormSeminormed b → UniformSpace.Completion (FormSeminormed b)) from
    UniformSpace.Completion.denseRange_coe
theorem formCompletionClasses_of_isPos {b : SesqForm 𝔛} (h : IsPosSesqForm b) :
    FormCompletionClasses b := by
  exact ⟨inferInstance, (formClass b).isLinear, inner_formClass h, LinearMap.range (formClass b),
    LinearMap.coe_range _, dense_range_formClass b⟩
end Forms
section Operators
variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
theorem isUnitaryOntoClosure_of_norm_eq [CompleteSpace H] (A : H →L[ℂ] H')
    (hA : ∀ ψ, ‖A ψ‖ = ‖ψ‖) {S : Set H} (hS : Dense S) {R : Set H'} (hR : A '' S = R) :
    IsUnitaryOntoClosure A R := by
  let L : H →ₗᵢ[ℂ] H' := ⟨A.toLinearMap, hA⟩
  have hL : ∀ ψ, L ψ = A ψ := fun _ => rfl
  have hinner : ∀ ψ ψ', inner ℂ (A ψ) (A ψ') = inner ℂ ψ ψ' := fun ψ ψ' => L.inner_map_map ψ ψ'
  have hclosed : IsClosed (Set.range A) := by
    have : Set.range A = Set.range L := by
      ext x
      simp only [Set.mem_range, hL]
    rw [this]
    exact L.isometry.isClosedEmbedding.isClosed_range
  have hrange : Set.range A = closure R := by
    apply Set.Subset.antisymm
    · rintro _ ⟨ψ, rfl⟩
      rw [← hR]
      exact image_closure_subset_closure_image A.continuous (mem_image_of_mem A (hS ψ))
    · apply closure_minimal _ hclosed
      rw [← hR]
      exact image_subset_range _ _
  refine ⟨hinner, hrange, LinearMap.range A.toLinearMap, ?_, ?_, ?_⟩
  · rw [LinearMap.coe_range]
    exact hrange
  · rw [LinearMap.coe_range]
    exact hclosed
  · refine ⟨A.toLinearMap.rangeRestrict, ⟨⟨?_, LinearMap.surjective_rangeRestrict _⟩, ?_⟩,
      fun ψ => rfl⟩
    · intro ψ ψ' e
      apply L.injective
      exact congrArg Subtype.val e
    · intro ψ ψ'
      exact hinner ψ ψ'
theorem extendsFromDenseSubmodule_holds [CompleteSpace H] [CompleteSpace H'] :
    ExtendsFromDenseSubmodule H H' := by
  intro D c a hD hc hb
  have hdr : DenseRange (D.subtypeL : D → H) := hD.denseRange_val
  have hui : IsUniformInducing (D.subtypeL : D → H) :=
    isUniformEmbedding_subtype_val.isUniformInducing
  let S : D →L[ℂ] H' := a.mkContinuous c hb
  let T : H →L[ℂ] H' := S.extend D.subtypeL
  have hT : ∀ ψ : D, T ψ = a ψ := fun ψ => ContinuousLinearMap.extend_eq S hdr hui ψ
  refine ⟨⟨T, hT, fun B hB => ?_⟩, fun A hA => ⟨?_, fun hn => ?_⟩⟩
  · apply ContinuousLinearMap.coeFn_injective
    refine Continuous.ext_on hD B.continuous T.continuous fun ψ hψ => ?_
    rw [hB ⟨ψ, hψ⟩, hT ⟨ψ, hψ⟩]
  · refine ContinuousLinearMap.opNorm_le_bound _ hc fun ψ => ?_
    refine forall_of_dense_of_isClosed hD (p := fun ψ => ‖A ψ‖ ≤ c * ‖ψ‖)
      (isClosed_le (by fun_prop) (by fun_prop)) (fun ψ hψ => ?_) ψ
    rw [hA ⟨ψ, hψ⟩]
    exact hb ⟨ψ, hψ⟩
  · have hnorm : ∀ ψ, ‖A ψ‖ = ‖ψ‖ := by
      refine forall_of_dense_of_isClosed hD (p := fun ψ => ‖A ψ‖ = ‖ψ‖)
        (isClosed_eq (by fun_prop) (by fun_prop)) fun ψ hψ => ?_
      rw [hA ⟨ψ, hψ⟩]
      exact hn ⟨ψ, hψ⟩
    refine isUnitaryOntoClosure_of_norm_eq A hnorm hD ?_
    ext χ
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      exact ⟨⟨ψ, hψ⟩, (hA ⟨ψ, hψ⟩).symm⟩
    · rintro ⟨ψ, rfl⟩
      exact ⟨ψ, ψ.2, hA ψ⟩
end Operators
section Classes
variable {𝔛 : Type*} [AddCommGroup 𝔛] [Module ℂ 𝔛]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
theorem extendsFromFormClasses_of_isPos {b : SesqForm 𝔛} (h : IsPosSesqForm b) :
    ExtendsFromFormClasses b H' := by
  intro c a hc hb
  have hker : LinearMap.ker (formClass b) ≤ LinearMap.ker a := by
    intro F hF
    rw [LinearMap.mem_ker] at hF ⊢
    have h₁ := norm_formClass_sq h F
    rw [hF, norm_zero] at h₁
    have h₂ := hb F
    rw [← h₁] at h₂
    have h₃ : ‖a F‖ ^ 2 ≤ 0 := by simpa using h₂
    have h₄ : ‖a F‖ ^ 2 = 0 := le_antisymm h₃ (by positivity)
    simpa using h₄
  let D : Submodule ℂ (FormCompletion b) := LinearMap.range (formClass b)
  let a' : D →ₗ[ℂ] H' :=
    ((LinearMap.ker (formClass b)).liftQ a hker) ∘ₗ
      ((formClass b).quotKerEquivRange.symm : D →ₗ[ℂ] _)
  have ha' : ∀ F (hF : formClass b F ∈ D), a' ⟨formClass b F, hF⟩ = a F := by
    intro F hF
    simp only [a', LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show (⟨formClass b F, hF⟩ : D) = ⟨formClass b F, LinearMap.mem_range_self _ F⟩ from rfl,
      LinearMap.quotKerEquivRange_symm_apply_image]
    simp
  have hmem : ∀ F, formClass b F ∈ D := fun F => LinearMap.mem_range_self _ F
  have hDense : Dense (D : Set (FormCompletion b)) := dense_range_formClass b
  have hbound : ∀ ψ : D, ‖a' ψ‖ ≤ c * ‖(ψ : FormCompletion b)‖ := by
    rintro ⟨_, F, rfl⟩
    rw [ha' F (hmem F)]
    have h₂ := hb F
    rw [← norm_formClass_sq h F, ← mul_pow] at h₂
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h₂
  have hc' := extendsFromDenseSubmodule_holds (H := FormCompletion b) (H' := H') D c a' hDense hc
    hbound
  have hon : ∀ A : FormCompletion b →L[ℂ] H', (∀ F, A (formClass b F) = a F) →
      ∀ ψ : D, A ψ = a' ψ := by
    rintro A hA ⟨_, F, rfl⟩
    rw [ha' F (hmem F)]
    exact hA F
  obtain ⟨⟨A₀, hA₀, huniq⟩, hall⟩ := hc'
  refine ⟨⟨A₀, fun F => ?_, fun B hB => huniq B (hon B hB)⟩, fun A hA => ?_⟩
  · rw [← ha' F (hmem F)]
    exact hA₀ ⟨formClass b F, hmem F⟩
  · obtain ⟨hn, hu⟩ := hall A (hon A hA)
    refine ⟨hn, fun he => ?_⟩
    have hr : Set.range a' = Set.range a := by
      ext χ
      constructor
      · rintro ⟨⟨_, F, rfl⟩, rfl⟩
        exact ⟨F, (ha' F (hmem F)).symm⟩
      · rintro ⟨F, rfl⟩
        exact ⟨⟨formClass b F, hmem F⟩, ha' F (hmem F)⟩
    rw [← hr]
    refine hu ?_
    rintro ⟨_, F, rfl⟩
    rw [ha' F (hmem F)]
    have h₂ := he F
    rw [← norm_formClass_sq h F] at h₂
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h₂
end Classes
section Polarization
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem inner_self_eq_ofReal_norm_sq (ψ : H) : inner ℂ ψ ψ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem inner_add_smul_apply_add_smul (A : H →L[ℂ] H) (ψ ψ' : H) (c : ℂ) :
    inner ℂ (ψ + c • ψ') (A (ψ + c • ψ')) =
      inner ℂ ψ (A ψ) + c * inner ℂ ψ (A ψ') + conj c * inner ℂ ψ' (A ψ) +
        conj c * c * inner ℂ ψ' (A ψ') := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  ring
theorem inner_apply_eq_polarization (A : H →L[ℂ] H) (ψ ψ' : H) :
    inner ℂ ψ' (A ψ) = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4, Complex.I ^ k *
      inner ℂ (ψ + Complex.I ^ k • ψ') (A (ψ + Complex.I ^ k • ψ')) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, inner_add_smul_apply_add_smul]
  have e₂ : Complex.I ^ 2 = -1 := Complex.I_sq
  have e₃ : Complex.I ^ 3 = -Complex.I := Complex.I_pow_three
  simp only [pow_zero, pow_one, e₂, e₃, map_one, map_neg, Complex.conj_I]
  linear_combination
    ((inner ℂ ψ' (A ψ) - inner ℂ ψ (A ψ')) / 2) * Complex.I_sq
theorem sum_norm_add_I_pow_smul_sq (ψ ψ' : H) :
    ∑ k ∈ Finset.range 4, ‖ψ + Complex.I ^ k • ψ'‖ ^ 2 = 4 * (‖ψ‖ ^ 2 + ‖ψ'‖ ^ 2) := by
  have p₁ := parallelogram_law_with_norm ℂ ψ ψ'
  have p₂ := parallelogram_law_with_norm ℂ ψ (Complex.I • ψ')
  have n : ‖Complex.I • ψ'‖ = ‖ψ'‖ := by simp [norm_smul]
  have e₂ : Complex.I ^ 2 = -1 := Complex.I_sq
  have e₃ : Complex.I ^ 3 = -Complex.I := Complex.I_pow_three
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, e₂, e₃, one_smul,
    neg_smul, zero_add, ← sub_eq_add_neg]
  rw [n] at p₂
  nlinarith [p₁, p₂]
theorem polarizationBounded_holds : PolarizationBounded H := by
  refine ⟨inner_apply_eq_polarization, fun A hA => ?_, fun A ε hε hA => ?_⟩
  · ext ψ
    have h := inner_apply_eq_polarization A ψ (A ψ)
    simp only [hA, mul_zero, Finset.sum_const_zero] at h
    simpa using h
  · have key : ∀ ψ ψ' : H, ‖inner ℂ ψ' (A ψ)‖ ≤ ε * (‖ψ‖ ^ 2 + ‖ψ'‖ ^ 2) := by
      intro ψ ψ'
      rw [inner_apply_eq_polarization A ψ ψ', norm_mul]
      have h₁ : ‖∑ k ∈ Finset.range 4, Complex.I ^ k *
          inner ℂ (ψ + Complex.I ^ k • ψ') (A (ψ + Complex.I ^ k • ψ'))‖ ≤
          ∑ k ∈ Finset.range 4, ε * ‖ψ + Complex.I ^ k • ψ'‖ ^ 2 := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
        exact hA _
      rw [← Finset.mul_sum, sum_norm_add_I_pow_smul_sq] at h₁
      have h₂ : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
      rw [h₂]
      linarith
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ψ => ?_
    by_cases h₀ : A ψ = 0
    · rw [h₀, norm_zero]
      positivity
    have hψ : ψ ≠ 0 := by
      rintro rfl
      exact h₀ (map_zero A)
    have hn : 0 < ‖A ψ‖ := norm_pos_iff.mpr h₀
    have hp : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
    have k := key ψ (((‖ψ‖ / ‖A ψ‖ : ℝ) : ℂ) • A ψ)
    have hN : ‖((‖ψ‖ / ‖A ψ‖ : ℝ) : ℂ) • A ψ‖ = ‖ψ‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      field_simp
    have hL : ‖inner ℂ (((‖ψ‖ / ‖A ψ‖ : ℝ) : ℂ) • A ψ) (A ψ)‖ = ‖ψ‖ * ‖A ψ‖ := by
      rw [inner_smul_left, Complex.conj_ofReal, inner_self_eq_ofReal_norm_sq, ← Complex.ofReal_mul,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      field_simp
    rw [hL, hN] at k
    have k₂ : ‖ψ‖ * ‖A ψ‖ ≤ ‖ψ‖ * (2 * ε * ‖ψ‖) := by nlinarith
    exact le_of_mul_le_mul_left k₂ hp
end Polarization
section Projections
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem apply_apply_of_isStarProjection {P : H →L[ℂ] H} (hP : IsStarProjection P) (ψ : H) :
    P (P ψ) = P ψ :=
  congrArg (fun T : H →L[ℂ] H => T ψ) hP.isIdempotentElem.eq
theorem inner_apply_of_isStarProjection {P : H →L[ℂ] H} (hP : IsStarProjection P) (ψ ψ' : H) :
    inner ℂ ψ (P ψ') = inner ℂ (P ψ) ψ' :=
  (isSelfAdjoint_iff_inner_eq P).mp hP.isSelfAdjoint ψ ψ'
theorem range_eq_fixedPoints_of_isStarProjection {P : H →L[ℂ] H} (hP : IsStarProjection P) :
    Set.range P = {ψ | P ψ = ψ} := by
  ext ψ
  constructor
  · rintro ⟨χ, rfl⟩
    exact apply_apply_of_isStarProjection hP χ
  · intro h
    exact ⟨ψ, h⟩
theorem orthProjRangeKer_holds : OrthProjRangeKer H := by
  refine ⟨fun P hP => ?_, fun P Q hP hQ hr => ?_⟩
  · have hfix := range_eq_fixedPoints_of_isStarProjection hP
    refine ⟨hfix, ⟨?_, LinearMap.range (P : H →ₗ[ℂ] H), ?_⟩, fun ψ => ?_, hP.one_sub, ?_, ?_⟩
    · rw [hfix]
      exact isClosed_eq P.continuous continuous_id
    · rw [LinearMap.coe_range]
      rfl
    · by_cases h₀ : P ψ = 0
      · rw [h₀, norm_zero]
        exact norm_nonneg _
      have hn : 0 < ‖P ψ‖ := norm_pos_iff.mpr h₀
      have h₁ : inner ℂ (P ψ) (P ψ) = inner ℂ ψ (P ψ) := by
        rw [← inner_apply_of_isStarProjection hP ψ (P ψ), apply_apply_of_isStarProjection hP]
      have h₂ : ‖P ψ‖ * ‖P ψ‖ ≤ ‖ψ‖ * ‖P ψ‖ := by
        have := norm_inner_le_norm (𝕜 := ℂ) ψ (P ψ)
        rw [← h₁, inner_self_eq_norm_sq_to_K] at this
        simpa [pow_two] using this
      exact le_of_mul_le_mul_right h₂ hn
    · ext ψ
      constructor
      · rintro ⟨χ, rfl⟩
        change P (χ - P χ) = 0
        rw [map_sub, apply_apply_of_isStarProjection hP, sub_self]
      · intro h
        refine ⟨ψ, ?_⟩
        change ψ - P ψ = ψ
        rw [show P ψ = 0 from h, sub_zero]
    · ext χ
      constructor
      · intro h
        rintro _ ⟨φ, rfl⟩
        rw [← inner_apply_of_isStarProjection hP, show P χ = 0 from h, inner_zero_right]
      · intro h
        have h₁ := h (P χ) ⟨χ, rfl⟩
        rw [← apply_apply_of_isStarProjection hP χ, ← inner_apply_of_isStarProjection hP] at h₁
        exact inner_self_eq_zero (𝕜 := ℂ).mp h₁
  · have h₁ : Q * P = P := by
      ext ψ
      have hm : P ψ ∈ Set.range Q := hr ▸ Set.mem_range_self ψ
      rw [range_eq_fixedPoints_of_isStarProjection hQ] at hm
      exact hm
    have h₂ : P * Q = Q := by
      ext ψ
      have hm : Q ψ ∈ Set.range P := hr ▸ Set.mem_range_self ψ
      rw [range_eq_fixedPoints_of_isStarProjection hP] at hm
      exact hm
    have h₃ := congrArg star h₁
    rw [star_mul, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq, h₂] at h₃
    exact h₃.symm
theorem selfAdjointCriteria_holds : SelfAdjointCriteria H := by
  refine ⟨fun A D hD hs => ?_, fun A B hA hB hc => (hA.commute_iff hB).mp hc,
    fun J hJ hJJ hpos => ?_⟩
  · have hsa : IsSelfAdjoint A := by
      rw [isSelfAdjoint_iff_inner_eq]
      intro ψ ψ'
      have step : ∀ ψ' ∈ (D : Set H), inner ℂ ψ (A ψ') = inner ℂ (A ψ) ψ' := by
        intro ψ' hψ'
        refine forall_of_dense_of_isClosed hD (p := fun ψ => inner ℂ ψ (A ψ') = inner ℂ (A ψ) ψ')
          (isClosed_eq (by fun_prop) (by fun_prop)) (fun ψ hψ => hs ψ hψ ψ' hψ') ψ
      exact forall_of_dense_of_isClosed hD (p := fun ψ' => inner ℂ ψ (A ψ') = inner ℂ (A ψ) ψ')
        (isClosed_eq (by fun_prop) (by fun_prop)) step ψ'
    refine ⟨hsa, fun hp => ?_⟩
    rw [le_iff_inner_sub_nonneg hsa (IsSelfAdjoint.zero _)]
    intro ψ
    rw [sub_zero]
    refine forall_of_dense_of_isClosed hD (p := fun ψ => 0 ≤ inner ℂ ψ (A ψ)) ?_ hp ψ
    have : {ψ : H | 0 ≤ inner ℂ ψ (A ψ)} =
        {ψ | 0 ≤ (inner ℂ ψ (A ψ)).re} ∩ {ψ | (inner ℂ ψ (A ψ)).im = 0} := by
      ext ψ
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Complex.le_def, Complex.zero_re,
        Complex.zero_im]
      exact and_congr_right fun _ => eq_comm
    rw [this]
    exact (isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  · have hnn := (le_iff_inner_sub_nonneg hJ (IsSelfAdjoint.zero _)).mp hpos
    ext ψ
    have hJJψ : J (J ψ) = ψ := congrArg (fun T : H →L[ℂ] H => T ψ) hJJ
    let χ : H := ψ - J ψ
    have hχ : J χ = -χ := by
      simp only [χ, map_sub, hJJψ, neg_sub]
    have h₁ := hnn χ
    rw [sub_zero, hχ, inner_neg_right, inner_self_eq_ofReal_norm_sq] at h₁
    have h₂ : ‖χ‖ ^ 2 ≤ 0 := by
      have := (Complex.le_def.mp h₁).1
      rw [Complex.zero_re, Complex.neg_re, Complex.ofReal_re] at this
      linarith
    have h₃ : ‖χ‖ = 0 := by
      have : ‖χ‖ ^ 2 = 0 := le_antisymm h₂ (by positivity)
      simpa using this
    have h₄ : χ = 0 := norm_eq_zero.mp h₃
    have h₅ : ψ = J ψ := sub_eq_zero.mp h₄
    exact h₅.symm
end Projections
theorem formCompletionAndExtensionTheorem_proof : FormCompletionAndExtensionTheorem := by
  intro 𝔛 H H' _ _ _ _ _ _ _ _ b h
  exact ⟨sesqFormCauchySchwarz_of_isPos h, formCompletionClasses_of_isPos h,
    extendsFromDenseSubmodule_holds, extendsFromFormClasses_of_isPos h, polarizationBounded_holds,
    orthProjRangeKer_holds, selfAdjointCriteria_holds⟩
end DenseExtension
end YangMills.Construction.FormHilbert
