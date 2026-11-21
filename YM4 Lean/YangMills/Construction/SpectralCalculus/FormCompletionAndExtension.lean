import YangMills.Construction.SpectralCalculus.FormCompletionAndBoundedExtension
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.SpectralCalculus.FormCompletionAndExtension
variable {V : Type} [AddCommGroup V] [Module ℂ V] {b : V → V → ℂ}
omit [AddCommGroup V] [Module ℂ V] in
theorem formSeminorm_nonneg (b : V → V → ℂ) (x : V) : 0 ≤ formSeminorm b x :=
  Real.sqrt_nonneg _
theorem formSeminorm_eq_norm (hb : IsPosHermitianForm b) (x : V) :
    formSeminorm b x = ‖toFormSpace b x‖ := by
  rw [norm_formSpace, posHermitianPart_of_isPosHermitianForm hb]
  rfl
theorem inner_toFormSpace (hb : IsPosHermitianForm b) (x y : V) :
    inner ℂ (toFormSpace b x) (toFormSpace b y) = b x y := by
  have h : inner ℂ (toFormSpace b x) (toFormSpace b y) = posHermitianPart b x y := rfl
  rw [h, posHermitianPart_of_isPosHermitianForm hb]
theorem norm_apply_le_formSeminorm_mul (hb : IsPosHermitianForm b) (f h : V) :
    ‖b f h‖ ≤ formSeminorm b f * formSeminorm b h := by
  rw [← inner_toFormSpace hb f h, formSeminorm_eq_norm hb f, formSeminorm_eq_norm hb h]
  exact norm_inner_le_norm (𝕜 := ℂ) _ _
theorem formSeminorm_add_le_add (hb : IsPosHermitianForm b) (f h : V) :
    formSeminorm b (f + h) ≤ formSeminorm b f + formSeminorm b h := by
  rw [formSeminorm_eq_norm hb (f + h), formSeminorm_eq_norm hb f, formSeminorm_eq_norm hb h]
  exact norm_add_le (toFormSpace b f) (toFormSpace b h)
theorem formSeminorm_smul (hb : IsPosHermitianForm b) (a : ℂ) (x : V) :
    formSeminorm b (a • x) = ‖a‖ * formSeminorm b x := by
  rw [formSeminorm_eq_norm hb (a • x), formSeminorm_eq_norm hb x]
  exact norm_smul a (toFormSpace b x)
theorem apply_eq_zero_of_null_right (hb : IsPosHermitianForm b) (f : V) {h : V}
    (hh : IsNullForForm b h) : b f h = 0 := by
  have h₁ := norm_apply_le_formSeminorm_mul hb f h
  rw [show formSeminorm b h = 0 from hh, mul_zero] at h₁
  exact norm_eq_zero.mp (le_antisymm h₁ (norm_nonneg _))
theorem apply_eq_zero_of_null_left (hb : IsPosHermitianForm b) {f : V} (h : V)
    (hf : IsNullForForm b f) : b f h = 0 := by
  have h₁ := norm_apply_le_formSeminorm_mul hb f h
  rw [show formSeminorm b f = 0 from hf, zero_mul] at h₁
  exact norm_eq_zero.mp (le_antisymm h₁ (norm_nonneg _))
theorem formSeminorm_sq (hb : IsPosHermitianForm b) (x : V) :
    (formSeminorm b x : ℂ) ^ 2 = b x x := by
  have h := Complex.le_def.mp (hb.nonneg x)
  have h₁ : formSeminorm b x ^ 2 = (b x x).re := Real.sq_sqrt (by simpa using h.1)
  apply Complex.ext
  · rw [← Complex.ofReal_pow, Complex.ofReal_re, h₁]
  · rw [← Complex.ofReal_pow, Complex.ofReal_im]
    simpa using h.2
theorem sum_fourthRootsOfUnity (F : ℂ → ℂ) :
    ∑ l ∈ ({1, Complex.I, -1, -Complex.I} : Finset ℂ), F l =
      F 1 + F Complex.I + F (-1) + F (-Complex.I) := by
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · ring
  all_goals (simp [Complex.ext_iff]; try norm_num)
theorem polarization_formSeminorm (hb : IsPosHermitianForm b) (f h : V) :
    4 * b f h =
      ∑ l ∈ ({1, Complex.I, -1, -Complex.I} : Finset ℂ), l * (formSeminorm b (l • f + h) : ℂ) ^ 2 := by
  have hexp : ∀ l : ℂ, b (l • f + h) (l • f + h) =
      conj l * l * b f f + conj l * b f h + l * b h f + b h h := by
    intro l
    rw [hb.add_left, hb.smul_left, hb.add_right, hb.add_right, hb.smul_right, hb.smul_right]
    ring
  rw [sum_fourthRootsOfUnity (fun l => l * (formSeminorm b (l • f + h) : ℂ) ^ 2)]
  simp only [formSeminorm_sq hb, hexp, map_one, map_neg, Complex.conj_I]
  linear_combination (2 * (b f h - b h f)) * Complex.I_sq
theorem posFormBasics (hb : IsPosHermitianForm b) : PosFormBasics b where
  norm_le_mul := norm_apply_le_formSeminorm_mul hb
  formSeminorm_add_le := formSeminorm_add_le_add hb
  exists_submodule_null :=
    ⟨{ carrier := {f | IsNullForForm b f}
       add_mem' := fun {f h} hf hh => by
         have h₁ := formSeminorm_add_le_add hb f h
         rw [show formSeminorm b f = 0 from hf, show formSeminorm b h = 0 from hh, add_zero] at h₁
         exact le_antisymm h₁ (formSeminorm_nonneg b _)
       zero_mem' := by
         show formSeminorm b 0 = 0
         simpa using formSeminorm_smul hb (0 : ℂ) (0 : V)
       smul_mem' := fun a f hf => by
         show formSeminorm b (a • f) = 0
         rw [formSeminorm_smul hb, show formSeminorm b f = 0 from hf, mul_zero] }, fun _ => Iff.rfl⟩
  add_null := fun f h f₀ h₀ hf hh => by
    rw [hb.add_left, hb.add_right, hb.add_right, apply_eq_zero_of_null_right hb f hh,
      apply_eq_zero_of_null_left hb h hf, apply_eq_zero_of_null_left hb h₀ hf]
    ring
  polarization := polarization_formSeminorm hb
theorem isFormCauchy_posHermitianPart_iff (hb : IsPosHermitianForm b) (f : ℕ → V) :
    IsFormCauchy b f ↔ IsFormCauchy (posHermitianPart b) f := by
  rw [posHermitianPart_of_isPosHermitianForm hb]
theorem formEquivalent_posHermitianPart_iff (hb : IsPosHermitianForm b) (f h : ℕ → V) :
    FormEquivalent b f h ↔ FormEquivalent (posHermitianPart b) f h := by
  rw [posHermitianPart_of_isPosHermitianForm hb]
def constClassLinearMap (b : V → V → ℂ) : V →ₗ[ℂ] SeparatedCompletion b where
  toFun := constClass b
  map_add' x y := map_add (formNullSubmodule b).mkQ
    (toFormCauchySubmodule b _ (isFormCauchy_const b x))
    (toFormCauchySubmodule b _ (isFormCauchy_const b y))
  map_smul' a x := map_smul (formNullSubmodule b).mkQ a
    (toFormCauchySubmodule b _ (isFormCauchy_const b x))
theorem inner_constClass_eq_posHermitianPart (b : V → V → ℂ) (f h : V) :
    inner ℂ (constClass b f) (constClass b h) = posHermitianPart b f h :=
  tendsto_nhds_unique
    (tendsto_inner_seqClass b (isFormCauchy_const b f) (isFormCauchy_const b h))
    tendsto_const_nhds
theorem inner_constClass_eq (hb : IsPosHermitianForm b) (f h : V) :
    inner ℂ (constClass b f) (constClass b h) = b f h := by
  rw [inner_constClass_eq_posHermitianPart, posHermitianPart_of_isPosHermitianForm hb]
theorem norm_constClass (hb : IsPosHermitianForm b) (x : V) :
    ‖constClass b x‖ = formSeminorm b x := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_constClass_eq hb]
  rfl
theorem constClass_eq_iff_null_sub (hb : IsPosHermitianForm b) (f h : V) :
    constClass b f = constClass b h ↔ IsNullForForm b (f - h) := by
  have h₁ := seqClass_eq_seqClass_iff b (isFormCauchy_const b f)
    (isFormCauchy_const b h)
  have h₂ : FormEquivalent (posHermitianPart b) (fun _ : ℕ => f) (fun _ => h) ↔
      IsNullForForm b (f - h) := by
    rw [posHermitianPart_of_isPosHermitianForm hb]
    exact tendsto_const_nhds_iff
  exact h₁.trans h₂
theorem isometry_separatedCompletionEquiv (b : V → V → ℂ) : Isometry (separatedCompletionEquiv b) :=
  AddMonoidHomClass.isometry_of_norm _ fun _ => rfl
theorem separatedCompletionEquiv_constClass (b : V → V → ℂ) (x : V) :
    separatedCompletionEquiv b (constClass b x) =
      ((toFormSpace b x : FormSpace b) : FormCompletion b) :=
  (separatedCompletionEquiv_seqClass b _ _).trans
    (tendsto_nhds_unique (tendsto_seqLimit b _)
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => ((toFormSpace b x : FormSpace b) : FormCompletion b)) atTop _))
theorem seqDense_range_constClass (b : V → V → ℂ) : IsSeqDense (Set.range (constClass b)) := by
  intro v
  obtain ⟨f, hf, rfl⟩ := exists_eq_seqClass b v
  refine ⟨fun j => constClass b (f j), fun j => ⟨_, rfl⟩, ?_⟩
  rw [(isometry_separatedCompletionEquiv b).isEmbedding.isInducing.tendsto_nhds_iff]
  exact (tendsto_seqLimit b (toFormCauchySubmodule b f hf)).congr fun j =>
    (separatedCompletionEquiv_constClass b (f j)).symm
theorem denseRange_constClass (b : V → V → ℂ) : DenseRange (constClass b) :=
  (isSeqDense_iff_dense _).mp (seqDense_range_constClass b)
theorem tendsto_apply_inner_seqClass (hb : IsPosHermitianForm b) {f h : ℕ → V}
    (hf : IsFormCauchy (posHermitianPart b) f) (hh : IsFormCauchy (posHermitianPart b) h) :
    Tendsto (fun j => b (f j) (h j)) atTop
      (𝓝 (inner ℂ (seqClass b f hf) (seqClass b h hh))) :=
  (tendsto_inner_seqClass b hf hh).congr fun j => by
    rw [posHermitianPart_of_isPosHermitianForm hb]
theorem formSeminorm_add_smul_sub_le (hb : IsPosHermitianForm b) (a : ℂ) (f f' h h' : V) :
    formSeminorm b ((f + a • h) - (f' + a • h')) ≤
      formSeminorm b (f - f') + ‖a‖ * formSeminorm b (h - h') := by
  have e : (f + a • h) - (f' + a • h') = (f - f') + a • (h - h') := by module
  rw [e, ← formSeminorm_smul hb]
  exact formSeminorm_add_le_add hb _ _
theorem separatedCompletionBasics (hb : IsPosHermitianForm b) : SeparatedCompletionBasics b where
  isFormCauchy_add_smul := fun f h a hf hh => by
    rw [isFormCauchy_posHermitianPart_iff hb] at hf hh ⊢
    exact (mem_formCauchySubmodule b _).mp (Submodule.add_mem _
      ((mem_formCauchySubmodule b f).mpr hf)
      (Submodule.smul_mem _ a ((mem_formCauchySubmodule b h).mpr hh)))
  formEquivalent_add_smul := fun f f' h h' a _ _ _ _ e₁ e₂ => by
    have t₁ : Tendsto (fun j => formSeminorm b (f j - f' j)) atTop (𝓝 0) := e₁
    have t₂ : Tendsto (fun j => formSeminorm b (h j - h' j)) atTop (𝓝 0) := e₂
    refine squeeze_zero (fun j => formSeminorm_nonneg b _)
      (fun j => formSeminorm_add_smul_sub_le hb a (f j) (f' j) (h j) (h' j)) ?_
    simpa using t₁.add (t₂.const_mul ‖a‖)
  exists_tendsto_form := fun f h hf hh => by
    rw [isFormCauchy_posHermitianPart_iff hb] at hf hh
    exact ⟨_, tendsto_apply_inner_seqClass hb hf hh⟩
  limit_eq_of_formEquivalent := fun f f' h h' c c' hf hf' hh hh' e₁ e₂ t t' => by
    rw [isFormCauchy_posHermitianPart_iff hb] at hf hf' hh hh'
    rw [formEquivalent_posHermitianPart_iff hb] at e₁ e₂
    have s := tendsto_apply_inner_seqClass hb hf hh
    have s' := tendsto_apply_inner_seqClass hb hf' hh'
    rw [(seqClass_eq_seqClass_iff b hf hf').mpr e₁,
      (seqClass_eq_seqClass_iff b hh hh').mpr e₂] at s
    exact (tendsto_nhds_unique t s).trans (tendsto_nhds_unique t' s').symm
  seqClass_add_smul := fun _ _ a hf hh hs =>
    YangMills.Construction.SpectralCalculus.seqClass_add_smul b a hf hh hs
  tendsto_inner_seqClass := fun _ _ hf hh => tendsto_apply_inner_seqClass hb hf hh
  isCompleteForm := isCompleteForm_inner
  isLinearMap_constClass := ⟨(constClassLinearMap b).map_add, (constClassLinearMap b).map_smul⟩
  inner_constClass := inner_constClass_eq hb
  constClass_eq_constClass_iff := constClass_eq_iff_null_sub hb
  isSeqDense_range_constClass := seqDense_range_constClass b
theorem ext_constClass {S T : SeparatedCompletion b →L[ℂ] SeparatedCompletion b}
    (h : ∀ x, S (constClass b x) = T (constClass b x)) : S = T :=
  ContinuousLinearMap.coeFn_injective
    ((denseRange_constClass b).equalizer S.continuous T.continuous (funext h))
theorem exists_completionExtension (hb : IsPosHermitianForm b) {A : V →ₗ[ℂ] V} {c : ℝ}
    (hA : IsFormBoundedBy b A c) :
    ∃ T : SeparatedCompletion b →L[ℂ] SeparatedCompletion b, IsCompletionExtension b A T := by
  have hd : DenseRange (constClassLinearMap b) := denseRange_constClass b
  have hbd : ∃ C, ∀ x, ‖(constClassLinearMap b ∘ₗ A) x‖ ≤ C * ‖constClassLinearMap b x‖ :=
    ⟨c, fun x => by
      show ‖constClass b (A x)‖ ≤ c * ‖constClass b x‖
      rw [norm_constClass hb, norm_constClass hb]
      exact hA.2 x⟩
  exact ⟨(constClassLinearMap b ∘ₗ A).extendOfNorm (constClassLinearMap b),
    fun x => LinearMap.extendOfNorm_eq hd hbd x⟩
theorem completionExtensionBasics (hb : IsPosHermitianForm b) {A : V →ₗ[ℂ] V} {c : ℝ}
    (hA : IsFormBoundedBy b A c) : CompletionExtensionBasics b A c where
  constClass_map_eq := fun f h e => by
    rw [constClass_eq_iff_null_sub hb] at e ⊢
    have h₁ := hA.2 (f - h)
    rw [show formSeminorm b (f - h) = 0 from e, mul_zero, map_sub] at h₁
    exact le_antisymm h₁ (formSeminorm_nonneg b _)
  existsUnique_extension := by
    obtain ⟨T, hT⟩ := exists_completionExtension hb hA
    exact ⟨T, hT, fun S hS => ext_constClass fun x => by rw [hS x, hT x]⟩
  norm_le := fun T hT => T.opNorm_le_bound hA.1 fun v =>
    (denseRange_constClass b).induction_on v
      (isClosed_le (T.continuous.norm) (continuous_const.mul continuous_norm)) fun x => by
        rw [hT x, norm_constClass hb, norm_constClass hb]
        exact hA.2 x
  extension_comp := fun A' _ _ T T' S h₁ h₂ h₃ => ext_constClass fun x => by
    show S (constClass b x) = T (T' (constClass b x))
    rw [h₃ x, h₂ x, h₁ (A' x)]
    rfl
  extension_adjoint := fun A' _ _ T T' h₁ h₂ hadj u v =>
    (denseRange_constClass b).induction_on₂ (p := fun u v => inner ℂ (T u) v = inner ℂ u (T' v))
      (isClosed_eq ((T.continuous.comp continuous_fst).inner continuous_snd)
        (continuous_fst.inner (T'.continuous.comp continuous_snd)))
      (fun f h => by rw [h₁ f, h₂ h, inner_constClass_eq hb, inner_constClass_eq hb, hadj]) u v
  extension_isometry := fun hiso T hT v =>
    (denseRange_constClass b).induction_on v
      (isClosed_eq T.continuous.norm continuous_norm) fun x => by
        rw [hT x, norm_constClass hb, norm_constClass hb, hiso x]
theorem innerContinuousDenseExt (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    InnerContinuousDenseExt H where
  tendsto_inner := fun _ _ _ _ hu hv => hu.inner (𝕜 := ℂ) hv
  eq_of_eqOn_dense := fun S B B' hS h => ContinuousLinearMap.coeFn_injective
    (Continuous.ext_on ((isSeqDense_iff_dense S).mp hS) B.continuous B'.continuous h)
theorem formCompletionAndBoundedExtension_holds : FormCompletionAndBoundedExtension :=
  ⟨fun _ _ _ _ hb => ⟨posFormBasics hb, separatedCompletionBasics hb,
      fun _ _ hA => completionExtensionBasics hb hA⟩,
    fun H _ _ _ => innerContinuousDenseExt H⟩
end YangMills.Construction.SpectralCalculus.FormCompletionAndExtension
