import YangMills.Construction.HilbertSpace.BoundedOperatorFactsProof
import YangMills.Construction.HilbertSpace.BasicFacts
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.HilbertSpaceFacts
open YangMills.Construction.HilbertSpaceBasics
theorem formSeminorm_eq_zero_of_mem {𝒱 : Type} {b : 𝒱 → 𝒱 → ℂ} {F : 𝒱} (hF : F ∈ formNullSet b) :
    formSeminorm b F = 0 := by
  have e : b F F = 0 := hF
  simp [formSeminorm, e]
section Sesquilinear
variable {𝒱 : Type} [AddCommGroup 𝒱] [Module ℂ 𝒱]
theorem sesq_add_smul {β : 𝒱 → 𝒱 → ℂ} (h : IsSesquilinear β) (F F' : 𝒱) (w : ℂ) :
    β (F + w • F') (F + w • F') =
      β F F + w * β F F' + conj w * β F' F + conj w * w * β F' F' := by
  rw [h.add_left, h.add_right, h.add_right, h.smul_right, h.smul_left, h.smul_left, h.smul_right]
  ring
theorem polarization_holds : Polarization := by
  intro 𝒱 _ _ β h F F'
  have i2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have i3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, i2]; ring
  have m2 : (-Complex.I) ^ 2 = -1 := by rw [neg_sq, i2]
  have m3 : (-Complex.I) ^ 3 = Complex.I := by rw [pow_succ, m2]; ring
  have e₁ : β (F + (1 : ℂ) • F') (F + (1 : ℂ) • F') = β F F + β F F' + β F' F + β F' F' := by
    rw [sesq_add_smul h]
    simp only [map_one]
    ring
  have e₂ : β (F + Complex.I • F') (F + Complex.I • F') =
      β F F + Complex.I * β F F' - Complex.I * β F' F + β F' F' := by
    rw [sesq_add_smul h, Complex.conj_I]
    linear_combination (-β F' F') * Complex.I_sq
  have e₃ : β (F + (-1 : ℂ) • F') (F + (-1 : ℂ) • F') = β F F - β F F' - β F' F + β F' F' := by
    rw [sesq_add_smul h]
    simp only [map_neg, map_one]
    ring
  have e₄ : β (F + (-Complex.I) • F') (F + (-Complex.I) • F') =
      β F F - Complex.I * β F F' + Complex.I * β F' F + β F' F' := by
    rw [sesq_add_smul h]
    simp only [map_neg, Complex.conj_I, neg_neg]
    linear_combination (-β F' F') * Complex.I_sq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, i2, i3, m2, m3, e₁,
    e₂, e₃, e₄, zero_add, one_mul]
  linear_combination (2 * (β F F' - β F' F)) * Complex.I_sq
theorem formEqOfDiagEq_holds : FormEqOfDiagEq := by
  intro 𝒱 _ _ β β' h h' hd
  funext F F'
  have e₁ := polarization_holds 𝒱 β h F F'
  have e₂ := polarization_holds 𝒱 β' h' F F'
  simp only [hd] at e₁
  exact mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0) (e₁.trans e₂.symm)
theorem formHermitianOfRealDiag_holds : FormHermitianOfRealDiag := by apply _root_.YangMills.Construction.BoundedOperators.sesquilinear_conj_symm_of_im_diag <;> assumption
end Sesquilinear
section CompletionClass
variable {𝒱 : Type} [AddCommGroup 𝒱] [Module ℂ 𝒱] {b : 𝒱 → 𝒱 → ℂ}
  (h : IsPosSemidef b)
include h
theorem inner_completionClass (F F' : 𝒱) :
    ⟪completionClass b h F, completionClass b h F'⟫_ℂ = b F F' :=
  UniformSpace.Completion.inner_coe (E := FormSpace b h) (𝕜 := ℂ) F F'
theorem norm_completionClass (F : 𝒱) : ‖completionClass b h F‖ = formSeminorm b F :=
  UniformSpace.Completion.norm_coe (E := FormSpace b h) F
theorem completionClass_eq_iff (F F' : 𝒱) :
    completionClass b h F = completionClass b h F' ↔ F - F' ∈ formNullSet b := by
  rw [← sub_eq_zero, ← map_sub, ← inner_self_eq_zero (𝕜 := ℂ), inner_completionClass h]
  rfl
theorem denseRange_completionClass : DenseRange (completionClass b h) :=
  UniformSpace.Completion.denseRange_coe (α := FormSpace b h)
theorem mem_formNullSet_of_formSeminorm_eq_zero {F : 𝒱} (hF : formSeminorm b F = 0) :
    F ∈ formNullSet b := by
  have e := (completionClass_eq_iff h F 0).1
    (by rw [map_zero, ← norm_eq_zero, norm_completionClass h]; exact hF)
  simpa using e
theorem norm_le_formSeminorm_mul (F F' : 𝒱) :
    ‖b F F'‖ ≤ formSeminorm b F * formSeminorm b F' := by
  rw [← inner_completionClass h, ← norm_completionClass h, ← norm_completionClass h]
  exact norm_inner_le_norm _ _
theorem mem_formNullSet_iff (F : 𝒱) : F ∈ formNullSet b ↔ ∀ F', b F' F = 0 := by
  refine ⟨fun hF F' => ?_, fun hF => hF F⟩
  have e := norm_le_formSeminorm_mul h F' F
  rw [formSeminorm_eq_zero_of_mem hF, mul_zero] at e
  exact norm_le_zero_iff.1 e
theorem isFormCauchy_iff (F : ℕ → 𝒱) :
    IsFormCauchy b F ↔ CauchySeq fun r => completionClass b h (F r) := by
  rw [Metric.cauchySeq_iff]
  constructor
  · intro hF ε hε
    obtain ⟨r, hr⟩ := hF (ε / 2) (half_pos hε)
    refine ⟨r, fun s hs s' hs' => ?_⟩
    show dist (completionClass b h (F s)) (completionClass b h (F s')) < ε
    rw [dist_eq_norm, ← map_sub, norm_completionClass h]
    exact (hr s s' hs hs').trans_lt (half_lt_self hε)
  · intro hF ε hε
    obtain ⟨r, hr⟩ := hF ε hε
    refine ⟨r, fun s s' hs hs' => ?_⟩
    have e : dist (completionClass b h (F s)) (completionClass b h (F s')) < ε := hr s hs s' hs'
    rw [dist_eq_norm, ← map_sub, norm_completionClass h] at e
    exact e.le
end CompletionClass
theorem seminormAndQuotient_holds : SeminormAndQuotient := by
  intro 𝒱 _ _ b h
  have hinv : ∀ F F', ∀ F₀ ∈ formNullSet b, ∀ F₀' ∈ formNullSet b,
      b (F + F₀) (F' + F₀') = b F F' := by
    intro F F' F₀ h₀ F₀' h₀'
    have a₁ : b F F₀' = 0 := (mem_formNullSet_iff h F₀').1 h₀' F
    have a₂ : b F₀ F₀' = 0 := (mem_formNullSet_iff h F₀').1 h₀' F₀
    have a₃ : b F₀ F' = 0 := by
      rw [h.isHermitianForm F' F₀, (mem_formNullSet_iff h F₀).1 h₀ F', map_zero]
    rw [h.add_left, h.add_right, h.add_right, a₁, a₂, a₃]
    ring
  obtain ⟨N, hN⟩ : ∃ N : Submodule ℂ 𝒱, (N : Set 𝒱) = formNullSet b := by
    refine ⟨{ carrier := formNullSet b, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, rfl⟩
    · intro F G hF hG
      refine (mem_formNullSet_iff h _).2 fun F' => ?_
      rw [h.add_right, (mem_formNullSet_iff h F).1 hF, (mem_formNullSet_iff h G).1 hG, add_zero]
    · refine (mem_formNullSet_iff h _).2 fun F' => ?_
      have e := h.smul_right 0 F' 0
      simpa using e
    · intro z F hF
      refine (mem_formNullSet_iff h _).2 fun F' => ?_
      rw [h.smul_right, (mem_formNullSet_iff h F).1 hF, mul_zero]
  have hmem : ∀ F, F ∈ N ↔ F ∈ formNullSet b := fun F => by rw [← hN]; rfl
  refine ⟨norm_le_formSeminorm_mul h, ?_, ?_, ?_, ?_, hinv, N, hN, ?_⟩
  · intro F F'
    simp only [← norm_completionClass h, map_add]
    exact norm_add_le _ _
  · intro z F
    simp only [← norm_completionClass h, map_smul]
    exact norm_smul _ _
  · intro F F'
    simp only [← norm_completionClass h, map_add, map_sub]
    have e := parallelogram_law_with_norm ℂ (completionClass b h F) (completionClass b h F')
    nlinarith [e]
  · ext F
    exact mem_formNullSet_iff h F
  · have hs := N.mkQ_surjective
    let rep : 𝒱 ⧸ N → 𝒱 := Function.surjInv hs
    have hrep : ∀ x, N.mkQ (rep x) = x := Function.surjInv_eq hs
    have hsub : ∀ F, rep (N.mkQ F) - F ∈ formNullSet b := fun F =>
      (hmem _).1 ((Submodule.Quotient.eq N).1 (hrep (N.mkQ F)))
    have hq : ∀ F F', b (rep (N.mkQ F)) (rep (N.mkQ F')) = b F F' := by
      intro F F'
      have e := hinv F F' _ (hsub F) _ (hsub F')
      rwa [add_sub_cancel, add_sub_cancel] at e
    refine ⟨fun x y => b (rep x) (rep y), ?_, hq⟩
    have hform : IsSesquilinear fun x y => b (rep x) (rep y) :=
      { add_left := by
          intro x₁ x₂ y
          obtain ⟨F₁, rfl⟩ := hs x₁
          obtain ⟨F₂, rfl⟩ := hs x₂
          obtain ⟨G, rfl⟩ := hs y
          simp only [← map_add, hq, h.add_left]
        smul_left := by
          intro z x y
          obtain ⟨F, rfl⟩ := hs x
          obtain ⟨G, rfl⟩ := hs y
          simp only [← map_smul, hq, h.smul_left]
        add_right := by
          intro x y₁ y₂
          obtain ⟨F, rfl⟩ := hs x
          obtain ⟨G₁, rfl⟩ := hs y₁
          obtain ⟨G₂, rfl⟩ := hs y₂
          simp only [← map_add, hq, h.add_right]
        smul_right := by
          intro z x y
          obtain ⟨F, rfl⟩ := hs x
          obtain ⟨G, rfl⟩ := hs y
          simp only [← map_smul, hq, h.smul_right] }
    have hpos : IsPosSemidef fun x y => b (rep x) (rep y) :=
      { hform with nonneg := fun x => h.nonneg _ }
    refine { hpos with definite := ?_ }
    intro x hx
    obtain ⟨F, rfl⟩ := hs x
    have e : b F F = 0 := (hq F F).symm.trans hx
    have e' : F ∈ N := (hmem F).2 e
    exact (Submodule.Quotient.mk_eq_zero N).2 e'
theorem completionProperties_holds : CompletionProperties := by
  intro 𝒱 _ _ b h
  refine ⟨inferInstance, inner_completionClass h, completionClass_eq_iff h, ?_, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.coe_range]
    exact denseRange_completionClass h
  · intro F
    refine ⟨(isFormCauchy_iff h _).2 (cauchySeq_const _), tendsto_const_nhds⟩
  · intro F hF
    obtain ⟨ξ, hξ⟩ := cauchySeq_tendsto_of_complete ((isFormCauchy_iff h F).1 hF)
    exact ⟨ξ, hF, hξ⟩
  · intro ξ
    have hex : ∀ r : ℕ, ∃ F, dist ξ (completionClass b h F) < 1 / ((r : ℝ) + 1) := fun r =>
      (denseRange_completionClass h).exists_dist_lt ξ (by positivity)
    choose F hF using hex
    have ht : Tendsto (fun r => completionClass b h (F r)) atTop (𝓝 ξ) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun _ => dist_nonneg) (fun r => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [dist_comm]
      exact (hF r).le
    exact ⟨F, (isFormCauchy_iff h F).2 ht.cauchySeq, ht⟩
  · intro ξ ξ' F F' hξ hξ'
    have hsub : Tendsto (fun r => formSeminorm b (F r - F' r)) atTop (𝓝 ‖ξ - ξ'‖) := by
      refine (hξ.2.sub hξ'.2).norm.congr fun r => ?_
      rw [← map_sub, norm_completionClass h]
    refine ⟨⟨fun e => ?_, fun e => ?_⟩, ?_, ?_, fun z => ?_⟩
    · subst e
      rw [sub_self, norm_zero] at hsub
      exact hsub
    · exact sub_eq_zero.1 (norm_eq_zero.1 (tendsto_nhds_unique hsub e))
    · exact (Filter.Tendsto.inner (𝕜 := ℂ) hξ.2 hξ'.2).congr fun r => inner_completionClass h _ _
    · have ht : Tendsto (fun r => completionClass b h (F r + F' r)) atTop (𝓝 (ξ + ξ')) :=
        (hξ.2.add hξ'.2).congr fun r => (map_add _ _ _).symm
      exact ⟨(isFormCauchy_iff h _).2 ht.cauchySeq, ht⟩
    · have ht : Tendsto (fun r => completionClass b h (z • F r)) atTop (𝓝 (z • ξ)) :=
        (hξ.2.const_smul z).congr fun r => (map_smul _ _ _).symm
      exact ⟨(isFormCauchy_iff h _).2 ht.cauchySeq, ht⟩
theorem exists_unique_extension_of_denseRange {E ℋ : Type} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] (e f : E →ₗ[ℂ] ℋ)
    (hd : DenseRange e) (c : ℝ) (hc : 0 ≤ c) (hb : ∀ x, ‖f x‖ ≤ c * ‖e x‖) :
    ∃ A : ℋ →L[ℂ] ℋ, (∀ x, A (e x) = f x) ∧ ‖A‖ ≤ c ∧
      ∀ A' : ℋ →L[ℂ] ℋ, (∀ x, A' (e x) = f x) → A' = A := by
  refine ⟨f.extendOfNorm e, LinearMap.extendOfNorm_eq hd ⟨c, hb⟩,
    ContinuousLinearMap.opNorm_le_bound _ hc (LinearMap.norm_extendOfNorm_apply_le hd c hb),
    fun A' hA' => ?_⟩
  refine DFunLike.coe_injective (hd.equalizer A'.continuous (f.extendOfNorm e).continuous ?_)
  funext x
  simp only [Function.comp_apply, hA', LinearMap.extendOfNorm_eq hd ⟨c, hb⟩]
theorem denseExtension_holds : DenseExtension := by
  intro ℋ _ _ _ 𝒟 c A₀ hd hc hb
  refine exists_unique_extension_of_denseRange 𝒟.subtype A₀ ?_ c hc hb
  have e : Set.range 𝒟.subtype = (𝒟 : Set ℋ) := by
    ext x
    simp
  rw [DenseRange, e]
  exact hd
theorem completionOperatorExtension_holds : CompletionOperatorExtension := by
  intro 𝒱 _ _ b h c 𝒜 hc hb
  refine ⟨fun F hF => ?_, ?_⟩
  · have h₀ := formSeminorm_eq_zero_of_mem hF
    have h₁ : formSeminorm b (𝒜 F) = 0 :=
      le_antisymm (by simpa [h₀] using hb F) (Real.sqrt_nonneg _)
    exact mem_formNullSet_of_formSeminorm_eq_zero h h₁
  · refine exists_unique_extension_of_denseRange (completionClass b h)
      ((completionClass b h).comp 𝒜) (denseRange_completionClass h) c hc ?_
    intro F
    rw [LinearMap.comp_apply, norm_completionClass h, norm_completionClass h]
    exact hb F
section BoundedOps
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
theorem inner_apply_eq_inner_star_apply (A : ℋ →L[ℂ] ℋ) (φ ψ : ℋ) :
    ⟪φ, A ψ⟫_ℂ = ⟪star A φ, ψ⟫_ℂ := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
theorem inner_apply_eq_of_isSelfAdjoint {A : ℋ →L[ℂ] ℋ} (hA : IsSelfAdjoint A) (φ ψ : ℋ) :
    ⟪φ, A ψ⟫_ℂ = ⟪A φ, ψ⟫_ℂ := by
  rw [inner_apply_eq_inner_star_apply, hA.star_eq]
theorem im_inner_self_apply_eq_zero {A : ℋ →L[ℂ] ℋ} (hA : IsSelfAdjoint A) (ψ : ℋ) :
    (⟪ψ, A ψ⟫_ℂ).im = 0 := by
  refine Complex.conj_eq_iff_im.1 ?_
  rw [inner_conj_symm, inner_apply_eq_of_isSelfAdjoint hA]
theorem isSelfAdjoint_of_inner_apply {A : ℋ →L[ℂ] ℋ} (h : ∀ φ ψ, ⟪φ, A ψ⟫_ℂ = ⟪A φ, ψ⟫_ℂ) :
    IsSelfAdjoint A :=
  LinearMap.IsSymmetric.isSelfAdjoint fun φ ψ => (h φ ψ).symm
omit [CompleteSpace ℋ] in
theorem inner_self_eq_ofReal_norm_sq (φ : ℋ) : ⟪φ, φ⟫_ℂ = ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem le_of_sq_le_mul_of_nonneg {x a : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (h : x ^ 2 ≤ a * x) :
    x ≤ a := by
  rcases hx.eq_or_lt with e | e
  · rw [← e]
    exact ha
  · refine le_of_mul_le_mul_right ?_ e
    nlinarith [h]
end BoundedOps
theorem orthProjOntoClosed_holds : OrthProjOntoClosed := by
  intro ℋ _ _ _ ℳ hc
  have : CompleteSpace ℳ := hc.completeSpace_coe
  have hperp : ∀ x, x ∈ orthComplement (ℳ : Set ℋ) ↔ x ∈ ℳᗮ := fun x =>
    (Submodule.mem_orthogonal' ℳ x).symm
  have h₁ : ∀ ψ, ℳ.starProjection ψ ∈ ℳ := fun ψ => Submodule.starProjection_apply_mem ℳ ψ
  have h₂ : ∀ ψ, ψ - ℳ.starProjection ψ ∈ orthComplement (ℳ : Set ℋ) := fun ψ =>
    (hperp _).2 (Submodule.sub_starProjection_mem_orthogonal ψ)
  have hu : ∀ ψ ψ₁, ψ₁ ∈ ℳ → ψ - ψ₁ ∈ orthComplement (ℳ : Set ℋ) → ψ₁ = ℳ.starProjection ψ :=
    fun ψ ψ₁ m p => (Submodule.eq_starProjection_of_mem_orthogonal m ((hperp _).1 p)).symm
  have hproj : IsOrthProjOnto ℳ.starProjection (ℳ : Set ℋ) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (isSelfAdjoint_starProjection ℳ).star_eq.symm
    · ext ψ
      exact ((Submodule.starProjection_eq_self_iff).2 (h₁ ψ)).symm
    · ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact h₁ y
      · intro hx
        exact ⟨x, Submodule.starProjection_eq_self_iff.2 hx⟩
  have huniq : ∀ Q' : ℋ →L[ℂ] ℋ, IsOrthProjOnto Q' (ℳ : Set ℋ) →
      Q' = ℳ.starProjection := by
    rintro Q' ⟨⟨e₁, e₂⟩, e₃⟩
    ext ψ
    have hfix : Q' (Q' ψ) = Q' ψ := (DFunLike.congr_fun e₂ ψ).symm
    refine hu ψ (Q' ψ) (by rw [← SetLike.mem_coe, ← e₃]; exact ⟨ψ, rfl⟩) ?_
    intro u hu'
    rw [← e₃] at hu'
    obtain ⟨v, rfl⟩ := hu'
    rw [inner_apply_eq_inner_star_apply, ← e₁, map_sub, hfix, sub_self, inner_zero_left]
  refine ⟨fun ψ => ⟨ℳ.starProjection ψ, ⟨h₁ ψ, h₂ ψ⟩, fun y hy => hu ψ y hy.1 hy.2⟩,
    ℳ.starProjection, fun ψ => ⟨h₁ ψ, h₂ ψ⟩, hproj, huniq, ?_⟩
  exact (huniq _ (Classical.epsilon_spec
    (p := fun Q : ℋ →L[ℂ] ℋ => IsOrthProjOnto Q (ℳ : Set ℋ)) ⟨_, hproj⟩)).symm
theorem denseOfOrthComplementTrivial_holds : DenseOfOrthComplementTrivial := by
  intro ℋ _ _ _
  have hbot : ∀ 𝒟 : Submodule ℂ ℋ, orthComplement (𝒟 : Set ℋ) = {0} → 𝒟ᗮ = ⊥ := by
    intro 𝒟 hp
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    have e : x ∈ orthComplement (𝒟 : Set ℋ) := (Submodule.mem_orthogonal' _ _).1 hx
    rw [hp] at e
    exact e
  refine ⟨fun ℳ hc hp => ?_, fun 𝒟 hp => ?_⟩
  · have : CompleteSpace ℳ := hc.completeSpace_coe
    exact Submodule.orthogonal_eq_bot_iff.1 (hbot ℳ hp)
  · exact 𝒟.dense_iff_topologicalClosure_eq_top.2
      (Submodule.topologicalClosure_eq_top_iff.2 (hbot 𝒟 hp))
theorem orthProjRange_holds : OrthProjRange := by
  rintro ℋ _ _ _ Q ⟨e₁, e₂⟩
  have hfix : ∀ ψ, Q (Q ψ) = Q ψ := fun ψ => (DFunLike.congr_fun e₂ ψ).symm
  have hr : Set.range Q = {ψ | Q ψ = ψ} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hfix y
    · intro hx
      exact ⟨x, hx⟩
  have hin : ∀ ψ, ⟪ψ, Q ψ⟫_ℂ = ((‖Q ψ‖ ^ 2 : ℝ) : ℂ) := by
    intro ψ
    rw [← hfix ψ, inner_apply_eq_inner_star_apply, ← e₁, hfix, inner_self_eq_ofReal_norm_sq]
  refine ⟨?_, hr, fun ψ => ⟨hin ψ, ?_⟩⟩
  · rw [hr]
    exact isClosed_eq Q.continuous continuous_id
  · have h₁ : ‖Q ψ‖ ^ 2 ≤ ‖ψ‖ * ‖Q ψ‖ := by
      have e := norm_inner_le_norm (𝕜 := ℂ) ψ (Q ψ)
      rw [hin, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at e
      exact e
    exact pow_le_pow_left₀ (norm_nonneg _)
      (le_of_sq_le_mul_of_nonneg (norm_nonneg _) (norm_nonneg _) h₁) 2
theorem boundedFormRepresentation_holds : BoundedFormRepresentation := by
  intro ℋ _ _ _ β c hc hβ hb
  let f : ℋ →ₗ⋆[ℂ] ℋ →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) β hβ.add_left
      (fun z F F' => hβ.smul_left z F F') hβ.add_right (fun z F F' => hβ.smul_right z F F')
  let B₀ : ℋ →L⋆[ℂ] ℋ →L[ℂ] ℂ := f.mkContinuous₂ c hb
  let B : ℋ →L[ℂ] ℋ := star (InnerProductSpace.continuousLinearMapOfBilin B₀)
  have hrep : ∀ φ ψ, β φ ψ = ⟪φ, B ψ⟫_ℂ := by
    intro φ ψ
    rw [inner_apply_eq_inner_star_apply, star_star,
      InnerProductSpace.continuousLinearMapOfBilin_apply]
    rfl
  refine ⟨B, hrep, ContinuousLinearMap.opNorm_le_bound _ hc fun ψ => ?_, fun B' h' => ?_⟩
  · refine le_of_sq_le_mul_of_nonneg (by positivity) (norm_nonneg _) ?_
    have e := hb (B ψ) ψ
    have e₂ : ‖β (B ψ) ψ‖ = ‖B ψ‖ ^ 2 := by
      rw [hrep, inner_self_eq_ofReal_norm_sq, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    linarith
  · ext ψ
    refine ext_inner_left ℂ fun φ => ?_
    rw [← h', ← hrep]
theorem boundedAdjointProperties_holds : BoundedAdjointProperties := by
  intro ℋ _ _ _ A B
  refine ⟨inner_apply_eq_inner_star_apply A, fun h => ?_, norm_star A, star_star A,
    star_mul A B, star_add A B, fun z => star_smul z A⟩
  ext φ
  refine ext_inner_right ℂ fun ψ => ?_
  rw [← h, inner_apply_eq_inner_star_apply]
theorem boundedOpDiagonal_holds : BoundedOpDiagonal := by
  intro ℋ _ _ _ A
  refine ⟨fun B h => ?_, fun h => ?_⟩
  · have e : ((A - B : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ) = 0 := by
      refine (inner_map_self_eq_zero _).1 fun x => ?_
      rw [← inner_conj_symm]
      simp [inner_sub_right, h x]
    ext x
    have e' := LinearMap.congr_fun e x
    simpa [sub_eq_zero] using e'
  · refine LinearMap.IsSymmetric.isSelfAdjoint
      ((LinearMap.isSymmetric_iff_inner_map_self_real _).2 fun v => ?_)
    rw [inner_conj_symm]
    have e : conj ⟪v, A v⟫_ℂ = ⟪v, A v⟫_ℂ := Complex.conj_eq_iff_im.2 (h v)
    rw [inner_conj_symm] at e
    exact e.symm
section PositiveOps
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
theorem isPosSemidef_of_isPositiveOp {A : ℋ →L[ℂ] ℋ} (hA : IsPositiveOp A) :
    IsPosSemidef fun φ ψ => ⟪φ, A ψ⟫_ℂ :=
  { add_left := fun F₁ F₂ F' => inner_add_left _ _ _
    smul_left := fun z F F' => inner_smul_left _ _ _
    add_right := fun F F₁ F₂ => by simp only [map_add, inner_add_right]
    smul_right := fun z F F' => by simp only [map_smul, inner_smul_right]
    nonneg := hA.2 }
theorem apply_eq_zero_of_inner_self_apply_eq_zero {A : ℋ →L[ℂ] ℋ} (hA : IsPositiveOp A) {ψ : ℋ}
    (h : ⟪ψ, A ψ⟫_ℂ = 0) : A ψ = 0 := by
  have hp := isPosSemidef_of_isPositiveOp hA
  have e : ⟪A ψ, A ψ⟫_ℂ = 0 :=
    (mem_formNullSet_iff hp ψ).1 h (A ψ)
  exact inner_self_eq_zero.1 e
theorem ofReal_norm_apply_sq_eq_inner (B : ℋ →L[ℂ] ℋ) (ψ : ℋ) :
    ((‖B ψ‖ ^ 2 : ℝ) : ℂ) = ⟪ψ, (star B * B) ψ⟫_ℂ := by
  show _ = ⟪ψ, star B (B ψ)⟫_ℂ
  rw [inner_apply_eq_inner_star_apply, star_star, inner_self_eq_ofReal_norm_sq]
end PositiveOps
theorem positiveOpCauchySchwarz_holds : PositiveOpCauchySchwarz := by
  intro ℋ _ _ _ A hA
  refine ⟨fun φ ψ => ?_, fun ψ => apply_eq_zero_of_inner_self_apply_eq_zero hA⟩
  have hp := isPosSemidef_of_isPositiveOp hA
  have e := norm_le_formSeminorm_mul hp φ ψ
  have r₁ := Complex.le_def.1 (hA.2 φ)
  have r₂ := Complex.le_def.1 (hA.2 ψ)
  simp only [Complex.zero_re, Complex.zero_im] at r₁ r₂
  have c₁ : ⟪φ, A φ⟫_ℂ = (((⟪φ, A φ⟫_ℂ).re : ℝ) : ℂ) := Complex.ext rfl (by simp [← r₁.2])
  have c₂ : ⟪ψ, A ψ⟫_ℂ = (((⟪ψ, A ψ⟫_ℂ).re : ℝ) : ℂ) := Complex.ext rfl (by simp [← r₂.2])
  rw [c₁, c₂, ← Complex.ofReal_mul, Complex.real_le_real]
  have s₁ : formSeminorm (fun φ ψ => ⟪φ, A ψ⟫_ℂ) φ ^ 2 = (⟪φ, A φ⟫_ℂ).re := Real.sq_sqrt r₁.1
  have s₂ : formSeminorm (fun φ ψ => ⟪φ, A ψ⟫_ℂ) ψ ^ 2 = (⟪ψ, A ψ⟫_ℂ).re := Real.sq_sqrt r₂.1
  rw [← s₁, ← s₂, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) e 2
theorem selfAdjointNormBounds_holds : SelfAdjointNormBounds := by
  intro ℋ _ _ _ A c hA hc
  have hsa : ∀ r : ℝ, IsSelfAdjoint ((r : ℂ) • (1 : ℋ →L[ℂ] ℋ)) := by
    intro r
    rw [IsSelfAdjoint, star_smul, star_one, Complex.star_def, Complex.conj_ofReal]
  have hsc : ∀ (r : ℝ) (ψ : ℋ),
      ⟪ψ, ((r : ℂ) • (1 : ℋ →L[ℂ] ℋ)) ψ⟫_ℂ = ((r * ‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    intro r ψ
    show ⟪ψ, (r : ℂ) • ψ⟫_ℂ = _
    rw [inner_smul_right, inner_self_eq_ofReal_norm_sq, Complex.ofReal_mul]
  have hbound : ∀ ψ, |(⟪ψ, A ψ⟫_ℂ).re| ≤ c * ‖ψ‖ ^ 2 := by
    intro ψ
    calc |(⟪ψ, A ψ⟫_ℂ).re| ≤ ‖⟪ψ, A ψ⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖ψ‖ * ‖A ψ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ψ‖ * (‖A‖ * ‖ψ‖) := by gcongr; exact A.le_opNorm ψ
      _ ≤ ‖ψ‖ * (c * ‖ψ‖) := by gcongr
      _ = c * ‖ψ‖ ^ 2 := by ring
  refine ⟨⟨hA, hsa _, hA.sub (hsa _), fun ψ => ?_⟩, ⟨hsa _, hA, (hsa _).sub hA, fun ψ => ?_⟩⟩
  · show 0 ≤ ⟪ψ, A ψ - (((-c : ℝ) : ℂ) • (1 : ℋ →L[ℂ] ℋ)) ψ⟫_ℂ
    rw [inner_sub_right, hsc, Complex.le_def]
    have b := abs_le.1 (hbound ψ)
    simp only [Complex.zero_re, Complex.zero_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, im_inner_self_apply_eq_zero hA ψ]
    constructor
    · linarith [b.1]
    · simp
  · show 0 ≤ ⟪ψ, (((c : ℝ) : ℂ) • (1 : ℋ →L[ℂ] ℋ)) ψ - A ψ⟫_ℂ
    rw [inner_sub_right, hsc, Complex.le_def]
    have b := abs_le.1 (hbound ψ)
    simp only [Complex.zero_re, Complex.zero_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, im_inner_self_apply_eq_zero hA ψ]
    constructor
    · linarith [b.2]
    · simp
theorem starMulMulPositive_holds : StarMulMulPositive := by
  intro ℋ _ _ _ B
  refine ⟨fun A hA => ⟨hA.1.conjugate' B, fun ψ => ?_⟩,
    ⟨IsSelfAdjoint.star_mul_self B, fun ψ => ?_⟩, ofReal_norm_apply_sq_eq_inner B⟩
  · have e : ⟪ψ, (star B * A * B) ψ⟫_ℂ = ⟪B ψ, A (B ψ)⟫_ℂ := by
      show ⟪ψ, star B (A (B ψ))⟫_ℂ = _
      rw [inner_apply_eq_inner_star_apply, star_star]
    rw [e]
    exact hA.2 _
  · rw [← ofReal_norm_apply_sq_eq_inner]
    exact_mod_cast sq_nonneg ‖B ψ‖
theorem positiveEqOfSqEq_holds : PositiveEqOfSqEq := by
  intro ℋ _ _ _ A B hA hB hc hs
  have hz : (A + B) * (A - B) = 0 := by
    have e : (A + B) * (A - B) = A ^ 2 - B ^ 2 + (B * A - A * B) := by noncomm_ring
    rw [e, hs, hc, sub_self, sub_self, add_zero]
  have hsa : IsSelfAdjoint (A - B) := hA.1.sub hB.1
  rw [← sub_eq_zero]
  ext ψ
  have h₀ : (A + B) ((A - B) ψ) = 0 := DFunLike.congr_fun hz ψ
  have hsum : ⟪(A - B) ψ, A ((A - B) ψ)⟫_ℂ + ⟪(A - B) ψ, B ((A - B) ψ)⟫_ℂ = 0 := by
    rw [← inner_add_right]
    have e : A ((A - B) ψ) + B ((A - B) ψ) = (A + B) ((A - B) ψ) := rfl
    rw [e, h₀, inner_zero_right]
  obtain ⟨a₁, a₂⟩ := (add_eq_zero_iff_of_nonneg (hA.2 _) (hB.2 _)).1 hsum
  have b₁ := apply_eq_zero_of_inner_self_apply_eq_zero hA a₁
  have b₂ := apply_eq_zero_of_inner_self_apply_eq_zero hB a₂
  have e' : (A - B) ((A - B) ψ) = 0 := by
    show A ((A - B) ψ) - B ((A - B) ψ) = 0
    rw [b₁, b₂, sub_self]
  have e : ⟪(A - B) ψ, (A - B) ψ⟫_ℂ = 0 := by
    rw [← inner_apply_eq_of_isSelfAdjoint hsa, e', inner_zero_right]
  exact inner_self_eq_zero.1 e
section NormalOps
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
omit [CompleteSpace ℋ] in
theorem mem_opKernel_ofBounded (A : ℋ →L[ℂ] ℋ) (x : ℋ) :
    x ∈ opKernel (ofBounded A) ↔ A x = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨⟨x, trivial⟩, h, rfl⟩
omit [CompleteSpace ℋ] in
theorem opRange_ofBounded (A : ℋ →L[ℂ] ℋ) :
    opRange (ofBounded A) = Set.range A := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y, trivial⟩, rfl⟩
end NormalOps
theorem normalOpKernelRange_holds : NormalOpKernelRange := by
  intro ℋ _ _ _ B hn
  have hnorm : ∀ ψ, ‖star B ψ‖ = ‖B ψ‖ := by
    intro ψ
    have e : ((‖star B ψ‖ ^ 2 : ℝ) : ℂ) = ((‖B ψ‖ ^ 2 : ℝ) : ℂ) := by
      rw [ofReal_norm_apply_sq_eq_inner, ofReal_norm_apply_sq_eq_inner, star_star, hn]
    have e' : ‖star B ψ‖ ^ 2 = ‖B ψ‖ ^ 2 := Complex.ofReal_injective e
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 e'
  have hker : opKernel (ofBounded (star B)) = opKernel (ofBounded B) := by
    ext x
    rw [mem_opKernel_ofBounded, mem_opKernel_ofBounded, ← norm_eq_zero, hnorm, norm_eq_zero]
  refine ⟨hker, fun hb => ?_⟩
  rw [opRange_ofBounded]
  have hd := (denseOfOrthComplementTrivial_holds ℋ).2 (LinearMap.range (B : ℋ →ₗ[ℂ] ℋ)) ?_
  · rw [LinearMap.coe_range] at hd
    exact hd
  · ext φ
    constructor
    · intro hφ
      have e : star B φ = 0 := by
        refine ext_inner_right ℂ fun ψ => ?_
        rw [← inner_apply_eq_inner_star_apply, inner_zero_left]
        exact hφ _ ⟨ψ, rfl⟩
      have e' : φ ∈ opKernel (ofBounded B) := by
        rw [← hker, mem_opKernel_ofBounded]
        exact e
      rw [hb] at e'
      exact e'
    · rintro rfl ψ -
      exact inner_zero_left _
theorem denseSubsetIdentities_holds : DenseSubsetIdentities := by
  intro ℋ _ _ _ 𝒟 hD
  have h₁ : ∀ A B A' B' : ℋ →L[ℂ] ℋ,
      (∀ φ ∈ 𝒟, ∀ ψ ∈ 𝒟, ⟪A φ, B ψ⟫_ℂ = ⟪A' φ, B' ψ⟫_ℂ) →
      ∀ φ ψ, ⟪A φ, B ψ⟫_ℂ = ⟪A' φ, B' ψ⟫_ℂ := by
    intro A B A' B' h φ ψ
    have c₁ : Continuous fun p : ℋ × ℋ => ⟪A p.1, B p.2⟫_ℂ :=
      (A.continuous.comp continuous_fst).inner (B.continuous.comp continuous_snd)
    have c₂ : Continuous fun p : ℋ × ℋ => ⟪A' p.1, B' p.2⟫_ℂ :=
      (A'.continuous.comp continuous_fst).inner (B'.continuous.comp continuous_snd)
    have e := Continuous.ext_on (hD.prod hD) c₁ c₂ fun p hp => h _ hp.1 _ hp.2
    exact congrFun e (φ, ψ)
  have h₃ : ∀ A B : ℋ →L[ℂ] ℋ, (∀ φ ∈ 𝒟, ∀ ψ ∈ 𝒟, ⟪φ, A ψ⟫_ℂ = ⟪φ, B ψ⟫_ℂ) → A = B := by
    intro A B h
    have e := h₁ 1 A 1 B (by simpa using h)
    ext ψ
    refine ext_inner_left ℂ fun φ => ?_
    simpa using e φ ψ
  refine ⟨h₁, fun A B h => ?_, h₃, fun A h => ?_, fun A hA h => ⟨hA, fun ψ => ?_⟩⟩
  · exact DFunLike.coe_injective (Continuous.ext_on hD A.continuous B.continuous h)
  · have e := h₁ 1 A A 1 (by simpa using h)
    exact isSelfAdjoint_of_inner_apply fun φ ψ => by simpa using e φ ψ
  · have hcl : IsClosed {ψ : ℋ | 0 ≤ ⟪ψ, A ψ⟫_ℂ} :=
      isClosed_le continuous_const (continuous_id.inner A.continuous)
    exact hcl.closure_subset_iff.2 h (hD ψ)
theorem denseSubsetStrongConvergence_holds : DenseSubsetStrongConvergence := by
  intro ℋ _ _ _ 𝒟 ι At l A hD hb h ψ
  obtain ⟨M, hM⟩ := hb
  have hM' : ∀ t, ‖At t‖ ≤ |M| := fun t => (hM ⟨t, rfl⟩).trans (le_abs_self M)
  have hK : 0 < |M| + ‖A‖ + 1 := by positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨φ, hφ, hd⟩ := hD.exists_dist_lt ψ (div_pos (half_pos hε) hK)
  filter_upwards [(Metric.tendsto_nhds.1 (h φ hφ)) (ε / 2) (half_pos hε)] with t ht
  rw [dist_eq_norm] at hd ht ⊢
  have e : At t ψ - A ψ = At t (ψ - φ) + (At t φ - A φ) - A (ψ - φ) := by
    simp only [map_sub]
    abel
  have n₁ : ‖At t (ψ - φ)‖ ≤ |M| * ‖ψ - φ‖ :=
    ((At t).le_opNorm _).trans (by gcongr; exact hM' t)
  have n₂ : ‖A (ψ - φ)‖ ≤ ‖A‖ * ‖ψ - φ‖ := A.le_opNorm _
  have n₃ : (|M| + ‖A‖ + 1) * ‖ψ - φ‖ < ε / 2 := by
    rwa [lt_div_iff₀ hK, mul_comm] at hd
  have n₄ := norm_nonneg (ψ - φ)
  calc ‖At t ψ - A ψ‖ ≤ ‖At t (ψ - φ) + (At t φ - A φ)‖ + ‖A (ψ - φ)‖ := by
        rw [e]
        exact norm_sub_le _ _
    _ ≤ ‖At t (ψ - φ)‖ + ‖At t φ - A φ‖ + ‖A (ψ - φ)‖ := by gcongr; exact norm_add_le _ _
    _ < ε := by nlinarith
theorem facts_hold : Facts :=
  ⟨polarization_holds, formEqOfDiagEq_holds, formHermitianOfRealDiag_holds,
    fun _ _ _ _ h => h.isHermitianForm, seminormAndQuotient_holds, completionProperties_holds,
    denseExtension_holds, completionOperatorExtension_holds, orthProjOntoClosed_holds,
    denseOfOrthComplementTrivial_holds, orthProjRange_holds, boundedFormRepresentation_holds,
    boundedAdjointProperties_holds, boundedOpDiagonal_holds, positiveOpCauchySchwarz_holds,
    selfAdjointNormBounds_holds, starMulMulPositive_holds, positiveEqOfSqEq_holds,
    normalOpKernelRange_holds, denseSubsetIdentities_holds, denseSubsetStrongConvergence_holds⟩
end YangMills.Construction.HilbertSpaceFacts
