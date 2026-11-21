import YangMills.Construction.Matrices.GluingFamiliesPreservesProductsOfHaarMeasuresForm
import YangMills.Construction.Matrices.OperatorsAreDeterminedByMatrixElementsForm
import YangMills.Construction.Matrices.PeterWeylFunctionsOfSeveralVariablesAndKernelsForm
import YangMills.Construction.Matrices.SeriesOfTheTensorOperatorConverges
import YangMills.Construction.Matrices.TensorOperatorOfAnIntegralOperator
import YangMills.Construction.Matrices.TensorProductsOfSquareIntegrableFunctions
import YangMills.Construction.TransferOperators.PeriodicStatesHaarMeasureCubicLatticesAndIntegralOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.HilbertSpaceBasics
noncomputable section
namespace YangMills.Construction.SpinHarmonics.TensorOneKernelOpProof
section
theorem integrable_mul_of_norm_le {W : Type*} [MeasurableSpace W] {ρ : Measure W} {b g : W → ℂ}
    (hb : AEStronglyMeasurable b ρ) {C : ℝ} (hC : ∀ x, ‖b x‖ ≤ C) (hg : Integrable g ρ) :
    Integrable (fun x => b x * g x) ρ := by
  refine Integrable.mono' (hg.norm.const_mul C) (hb.mul hg.1) (ae_of_all _ fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
variable {V Z : Type*} [MeasurableSpace V] [MeasurableSpace Z]
  {μ : Measure V} {ν : Measure Z} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
theorem sq_integral_norm_le_integral_sq {g : V → ℂ} (hg : MemLp g 2 μ) :
    (∫ x, ‖g x‖ ∂μ) ^ 2 ≤ ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have h1 : Integrable (fun x => ‖g x‖) μ := (hg.integrable one_le_two).norm
  have h2 : Integrable (fun x => ‖g x‖ ^ 2) μ := hg.integrable_norm_pow two_ne_zero
  set m := ∫ x, ‖g x‖ ∂μ with hm
  have h3 : 0 ≤ ∫ x, (‖g x‖ - m) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have h4 : ∫ x, (‖g x‖ - m) ^ 2 ∂μ = (∫ x, ‖g x‖ ^ 2 ∂μ) - 2 * m * m + m ^ 2 := by
    have e : ∀ x, (‖g x‖ - m) ^ 2 = ‖g x‖ ^ 2 - 2 * m * ‖g x‖ + m ^ 2 := fun x => by ring
    simp only [e]
    have i₁ : Integrable (fun x => ‖g x‖ ^ 2 - 2 * m * ‖g x‖) μ := h2.sub (h1.const_mul _)
    rw [integral_add i₁ (integrable_const _), integral_sub h2 (h1.const_mul _),
      integral_const_mul, ← hm]
    simp
  nlinarith
def kernelSlice (μ : Measure V) (K : V × V → ℂ) (f : V × Z → ℂ) (p : V × Z) : ℂ :=
  ∫ w, K (p.1, w) * f (w, p.2) ∂μ
theorem stronglyMeasurable_kernelSlice {K : V × V → ℂ} {f : V × Z → ℂ}
    (hK : StronglyMeasurable K) (hf : StronglyMeasurable f) :
    StronglyMeasurable (kernelSlice μ K f) := by
  have h₁ : StronglyMeasurable fun q : (V × Z) × V => K (q.1.1, q.2) :=
    hK.comp_measurable ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have h₂ : StronglyMeasurable fun q : (V × Z) × V => f (q.2, q.1.2) :=
    hf.comp_measurable (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  exact (h₁.mul h₂).integral_prod_right'
theorem memLp_kernelSlice {K : V × V → ℂ} {f : V × Z → ℂ}
    (hK : StronglyMeasurable K) {C : ℝ} (hC : ∀ p, ‖K p‖ ≤ C)
    (hf : StronglyMeasurable f) (hf2 : MemLp f 2 (μ.prod ν)) :
    MemLp (kernelSlice μ K f) 2 (μ.prod ν) := by
  have hG := stronglyMeasurable_kernelSlice (μ := μ) hK hf
  have hsq : Integrable (fun p : V × Z => ‖f p‖ ^ 2) (μ.prod ν) :=
    hf2.integrable_norm_pow two_ne_zero
  have hswap : Integrable (fun p : Z × V => ‖f (p.2, p.1)‖ ^ 2) (ν.prod μ) := hsq.swap
  have hsec : ∀ᵐ z ∂ν, MemLp (fun w => f (w, z)) 2 μ := by
    filter_upwards [hswap.prod_right_ae] with z hz
    exact (memLp_two_iff_integrable_sq_norm
      (hf.comp_measurable measurable_prodMk_right).aestronglyMeasurable).2 hz
  have hh : Integrable (fun z => ∫ w, ‖f (w, z)‖ ^ 2 ∂μ) ν := hswap.integral_prod_left
  have hbound : ∀ᵐ z ∂ν, ∀ v, ‖kernelSlice μ K f (v, z)‖ ^ 2 ≤
      C ^ 2 * ∫ w, ‖f (w, z)‖ ^ 2 ∂μ := by
    filter_upwards [hsec] with z hz v
    have h₁ : Integrable (fun w => ‖f (w, z)‖) μ := (hz.integrable one_le_two).norm
    have h₂ : ‖kernelSlice μ K f (v, z)‖ ≤ C * ∫ w, ‖f (w, z)‖ ∂μ := by
      rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le (h₁.const_mul C) (ae_of_all _ fun w => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    calc ‖kernelSlice μ K f (v, z)‖ ^ 2 ≤ (C * ∫ w, ‖f (w, z)‖ ∂μ) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h₂ 2
      _ = C ^ 2 * (∫ w, ‖f (w, z)‖ ∂μ) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (sq_integral_norm_le_integral_sq hz) (sq_nonneg C)
  refine (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).2 ?_
  refine Integrable.mono' ((hh.const_mul (C ^ 2)).comp_snd μ)
    (hG.norm.pow 2).aestronglyMeasurable ?_
  have hae := Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν) |>.ae hbound
  filter_upwards [hae] with p hp
  rw [Real.norm_of_nonneg (by positivity)]
  exact hp p.1
theorem integral_mul_kernelSlice {K : V × V → ℂ} {f : V × Z → ℂ}
    (hK : StronglyMeasurable K) {C : ℝ} (hC₀ : 0 ≤ C) (hC : ∀ p, ‖K p‖ ≤ C)
    (hf : StronglyMeasurable f) (hf2 : MemLp f 2 (μ.prod ν))
    {a : V → ℂ} {c : Z → ℂ} (ha : StronglyMeasurable a) (hc : StronglyMeasurable c)
    {A D : ℝ} (hA : ∀ v, ‖a v‖ ≤ A) (hD : ∀ z, ‖c z‖ ≤ D) :
    ∫ p, a p.1 * c p.2 * kernelSlice μ K f p ∂(μ.prod ν) =
      ∫ v, a v * ∫ w, K (v, w) * ∫ z, c z * f (w, z) ∂ν ∂μ ∂μ := by
  have hA₀ : 0 ≤ A := (norm_nonneg _).trans (hA (Classical.choice (μ.nonempty_of_neZero)))
  have hint : Integrable (fun p : V × Z => a p.1 * c p.2 * kernelSlice μ K f p)
      (μ.prod ν) := by
    refine integrable_mul_of_norm_le (C := A * D)
      ((ha.comp_measurable measurable_fst).mul
        (hc.comp_measurable measurable_snd)).aestronglyMeasurable (fun p => ?_)
      ((memLp_kernelSlice hK hC hf hf2).integrable one_le_two)
    rw [norm_mul]
    exact mul_le_mul (hA _) (hD _) (norm_nonneg _) hA₀
  rw [integral_prod _ hint]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  have e : ∀ z, a v * c z * kernelSlice μ K f (v, z) =
      a v * ∫ w, K (v, w) * (c z * f (w, z)) ∂μ := by
    intro z
    rw [mul_assoc, kernelSlice, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only
    ring
  simp only [e]
  rw [integral_const_mul]
  congr 1
  have hsw : Integrable (Function.uncurry fun (w : V) (z : Z) => K (v, w) * (c z * f (w, z)))
      (μ.prod ν) := by
    have hb : StronglyMeasurable fun q : V × Z => K (v, q.1) * c q.2 :=
      (hK.comp_measurable (measurable_prodMk_left.comp measurable_fst)).mul
        (hc.comp_measurable measurable_snd)
    have := integrable_mul_of_norm_le (C := C * D) hb.aestronglyMeasurable (fun q => ?_)
      (hf2.integrable one_le_two)
    · refine this.congr (ae_of_all _ fun q => ?_)
      simp only [Function.uncurry]
      ring
    · rw [norm_mul]
      exact mul_le_mul (hC _) (hD _) (norm_nonneg _) hC₀
  rw [← integral_integral_swap hsw]
  simp only [integral_const_mul]
end
section
variable {I : Type} [Countable I]
theorem toHaarL2_congr_ae {f g : (I → specialUnitary) → ℂ} (h : f =ᵐ[haarPi I] g) :
    toHaarL2 f = toHaarL2 g := by
  by_cases hf : MemLp f 2 (haarPi I)
  · have hg : MemLp g 2 (haarPi I) := (memLp_congr_ae h).1 hf
    unfold toHaarL2
    rw [dif_pos hf, dif_pos hg]
    exact (MemLp.toLp_eq_toLp_iff hf hg).2 h
  · have hg : ¬ MemLp g 2 (haarPi I) := fun hg => hf ((memLp_congr_ae h).2 hg)
    unfold toHaarL2
    rw [dif_neg hf, dif_neg hg]
theorem toHaarL2_coeFn (φ : HaarL2 I) : toHaarL2 (φ : (I → specialUnitary) → ℂ) = φ := by
  unfold toHaarL2
  rw [dif_pos (Lp.memLp φ)]
  exact Lp.toLp_coeFn φ _
theorem coeFn_toHaarL2 {f : (I → specialUnitary) → ℂ} (h : MemLp f 2 (haarPi I)) :
    (toHaarL2 f : (I → specialUnitary) → ℂ) =ᵐ[haarPi I] f := by
  unfold toHaarL2
  rw [dif_pos h]
  exact h.coeFn_toLp
end
section
variable {I : Type} [Finite I]
theorem peterWeylVec_ae_eq (α : PeterWeylIndex I) :
    (peterWeylVec α : (I → specialUnitary) → ℂ) =ᵐ[haarPi I] peterWeylFn α :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := haarPi I) (peterWeylFn α)
theorem memLp_peterWeylFn (α : PeterWeylIndex I) : MemLp (peterWeylFn α) 2 (haarPi I) :=
  (memLp_congr_ae (peterWeylVec_ae_eq α)).1 (Lp.memLp _)
theorem toHaarL2_peterWeylFn (α : PeterWeylIndex I) :
    toHaarL2 (peterWeylFn α) = peterWeylVec α :=
  (toHaarL2_congr_ae (peterWeylVec_ae_eq α).symm).trans (toHaarL2_coeFn _)
theorem integral_star_peterWeylFn_mul (γ : PeterWeylIndex I) (ω : HaarL2 I) :
    ∫ z, star (peterWeylFn γ z) * ω z ∂haarPi I =
      inner ℂ (peterWeylVec γ) ω := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [peterWeylVec_ae_eq γ] with z hz
  rw [hz]
  simp [RCLike.inner_apply, mul_comm]
theorem ext_inner_peterWeylVec [Nonempty I]
    (hD : AllOpsDeterminedByEntries) {a b : HaarL2 I}
    (h : ∀ α : PeterWeylIndex I, (inner ℂ (peterWeylVec α) a : ℂ) =
      inner ℂ (peterWeylVec α) b) : a = b := by
  have hAA : (innerSL ℂ (a - b)).smulRight a = (innerSL ℂ (a - b)).smulRight b := by
    refine hD I _ _ fun α α' => ?_
    simp only [peterWeylEntry, ContinuousLinearMap.smulRight_apply, inner_smul_right, h α]
  have h₁ := congrArg (fun T : HaarL2 I →L[ℂ] HaarL2 I => T (a - b)) hAA
  simp only [ContinuousLinearMap.smulRight_apply] at h₁
  have h₂ : (innerSL ℂ (a - b) (a - b) : ℂ) • (a - b) = 0 := by
    rw [smul_sub, sub_eq_zero]
    exact h₁
  rcases smul_eq_zero.1 h₂ with h₃ | h₃
  · exact sub_eq_zero.1 (inner_self_eq_zero.1 h₃)
  · exact sub_eq_zero.1 h₃
end
section
variable {J : Type} [Finite J] {B : Set J}
theorem measurePreserving_restrictTo_prod (hJ : GlueMeasurePreserving) :
    MeasurePreserving (fun u : J → specialUnitary => (restrictTo B u, restrictTo Bᶜ u))
      (haarPi J) ((haarPi ↥B).prod (haarPi ↥Bᶜ)) := by
  have hm : Measurable fun u : J → specialUnitary => (restrictTo B u, restrictTo Bᶜ u) :=
    (measurable_pi_lambda _ fun b => measurable_pi_apply _).prodMk
      (measurable_pi_lambda _ fun b => measurable_pi_apply _)
  refine ⟨hm, ?_⟩
  rw [← (hJ J B).map_eq, Measure.map_map hm (hJ J B).measurable]
  have h : (fun u : J → specialUnitary => (restrictTo B u, restrictTo Bᶜ u)) ∘
      (fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2) = id := by
    funext p
    exact (splitEquiv (X := specialUnitary) B).right_inv p
  rw [h, Measure.map_id]
omit [Finite J] in
theorem continuous_glue :
    Continuous fun q : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B q.1 q.2 := by
  refine continuous_pi fun b => ?_
  by_cases h : b ∈ B
  · have e : (fun q : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B q.1 q.2 b) =
        fun q => q.1 ⟨b, h⟩ := by
      funext q
      exact dif_pos h
    rw [e]
    exact (continuous_apply _).comp continuous_fst
  · have e : (fun q : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B q.1 q.2 b) =
        fun q => q.2 ⟨b, h⟩ := by
      funext q
      exact dif_neg h
    rw [e]
    exact (continuous_apply _).comp continuous_snd
theorem inner_peterWeylVec_tensorOne [Nonempty J]
    (hT : TensorFnMemL2Inner)
    (hS : TensorOneSeriesConvergesForAll)
    (hP : PeterWeylOrthonormalAndKernel)
    (hB : B.Nonempty) (hB' : B ≠ Set.univ)
    (X : HaarL2 ↥B →L[ℂ] HaarL2 ↥B) (F : HaarL2 J)
    (α : PeterWeylIndex ↥B) (γ : PeterWeylIndex ↥Bᶜ) :
    (inner ℂ (peterWeylVec (glue B α γ)) (tensorOne B X F) : ℂ) =
      inner ℂ (peterWeylVec α) (X (toHaarL2 (partialCoeff B γ F))) := by
  obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem B).1 hB'
  have : Nonempty ↥Bᶜ := ⟨⟨b, hb⟩⟩
  have hort : Orthonormal ℂ (peterWeylVec : PeterWeylIndex ↥Bᶜ → HaarL2 ↥Bᶜ) :=
    (hP ↥Bᶜ fun _ => ⟨0⟩).1
  have hnot : ¬ ∀ b, b ∈ B := fun h => hb (h b)
  obtain ⟨-, hsum, hval⟩ := (hS J B hB hB' X).1 F
  have hjoin : peterWeylVec (glue B α γ) =
      toHaarL2 (tensorFn B (peterWeylFn α) (peterWeylFn γ)) :=
    (toHaarL2_peterWeylFn _).symm.trans
      (congrArg toHaarL2 (funext fun u => peterWeylFn_glue B α γ u))
  have hterm : ∀ γ' : PeterWeylIndex ↥Bᶜ,
      (inner ℂ (peterWeylVec (glue B α γ)) (tensorSeriesTerm B X F γ') : ℂ) =
        inner ℂ (peterWeylVec α) (X (toHaarL2 (partialCoeff B γ' F))) *
          inner ℂ (peterWeylVec γ) (peterWeylVec γ') := by
    intro γ'
    have h := (hT J B (peterWeylFn α) (X (toHaarL2 (partialCoeff B γ' F)))
      (peterWeylFn γ) (peterWeylFn γ') (memLp_peterWeylFn α) (Lp.memLp _)
      (memLp_peterWeylFn γ) (memLp_peterWeylFn γ')).2
    simp only [toHaarL2_peterWeylFn, toHaarL2_coeFn] at h
    rw [hjoin, tensorSeriesTerm]
    exact h
  have hs : HasSum (fun γ' => (inner ℂ (peterWeylVec (glue B α γ))
      (tensorSeriesTerm B X F γ') : ℂ))
      (inner ℂ (peterWeylVec (glue B α γ)) (∑' γ', tensorSeriesTerm B X F γ')) :=
    hsum.hasSum.mapL (innerSL ℂ _)
  have hone := hasSum_single (f := fun γ' => (inner ℂ (peterWeylVec (glue B α γ))
      (tensorSeriesTerm B X F γ') : ℂ)) γ (fun γ' hne => by
    rw [hterm, hort.2 (Ne.symm hne), mul_zero])
  rw [hval, tensorOneApply, dif_neg hnot, hs.unique hone]
  rw [hterm, inner_self_eq_norm_sq_to_K, hort.1]
  simp
theorem tensorOne_ae_eq_integral [Nonempty J]
    (hJ : GlueMeasurePreserving)
    (hT : TensorFnMemL2Inner)
    (hS : TensorOneSeriesConvergesForAll)
    (hD : AllOpsDeterminedByEntries)
    (hP : PeterWeylOrthonormalAndKernel)
    (hK : TransferOperators.GibbsHaarKernels.Statement)
    (hB : B.Nonempty) (hB' : B ≠ Set.univ)
    (X : HaarL2 ↥B →L[ℂ] HaarL2 ↥B)
    (K : C((↥B → specialUnitary) × (↥B → specialUnitary), ℂ))
    (hX : X = Schatten.kernelOp (haarPi ↥B) K) (F : HaarL2 J) :
    ∀ᵐ u ∂haarPi J, tensorOne B X F u = ∫ w, K (restrictTo B u, w) *
      F (glue B w (restrictTo Bᶜ u)) ∂haarPi ↥B := by
  have : Nonempty ↥B := hB.to_subtype
  have hI : Schatten.HasKernel (haarPi ↥B) K X := by
    rw [hX]
    exact (hK.2.2.2 ↥B).1 K K.continuous |>.2.1
  let f : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) → ℂ := fun p => F (glue B p.1 p.2)
  have hfm : StronglyMeasurable f :=
    (Lp.stronglyMeasurable F).comp_measurable (hJ J B).measurable
  have hf2 : MemLp f 2 ((haarPi ↥B).prod (haarPi ↥Bᶜ)) :=
    (Lp.memLp F).comp_measurePreserving (hJ J B)
  have hKm : StronglyMeasurable (K : (↥B → specialUnitary) × (↥B → specialUnitary) → ℂ) :=
    K.continuous.stronglyMeasurable
  have hC : ∀ p, ‖K p‖ ≤ ‖K‖ := K.norm_coe_le_norm
  let G := kernelSlice (haarPi ↥B) K f
  have hsplit := measurePreserving_restrictTo_prod (B := B) hJ
  have hGm : StronglyMeasurable G := stronglyMeasurable_kernelSlice hKm hfm
  have hGJ : MemLp (fun u : J → specialUnitary => G (restrictTo B u, restrictTo Bᶜ u)) 2
      (haarPi J) := (memLp_kernelSlice hKm hC hfm hf2).comp_measurePreserving hsplit
  have hcoef : ∀ (α : PeterWeylIndex ↥B) (γ : PeterWeylIndex ↥Bᶜ),
      (inner ℂ (peterWeylVec (glue B α γ)) (tensorOne B X F) : ℂ) =
        inner ℂ (peterWeylVec (glue B α γ))
          (toHaarL2 fun u : J → specialUnitary => G (restrictTo B u, restrictTo Bᶜ u)) := by
    intro α γ
    have ha : StronglyMeasurable fun v => star (peterWeylFn α v) :=
      (continuous_star.comp (peterWeylFn α).continuous).stronglyMeasurable
    have hc : StronglyMeasurable fun z => star (peterWeylFn γ z) :=
      (continuous_star.comp (peterWeylFn γ).continuous).stronglyMeasurable
    have hA : ∀ v, ‖star (peterWeylFn α v)‖ ≤ ‖peterWeylFn α‖ := fun v => by
      rw [norm_star]
      exact (peterWeylFn α).norm_coe_le_norm v
    have hA' : ∀ z, ‖star (peterWeylFn γ z)‖ ≤ ‖peterWeylFn γ‖ := fun z => by
      rw [norm_star]
      exact (peterWeylFn γ).norm_coe_le_norm z
    have hpc : MemLp (partialCoeff B γ F) 2 (haarPi ↥B) :=
      (((hS J B hB hB' X).1 F).1 γ).1
    have e₁ : (inner ℂ (peterWeylVec α) (X (toHaarL2 (partialCoeff B γ F))) : ℂ) =
        ∫ v, star (peterWeylFn α v) *
          ∫ w, K (v, w) * ∫ z, star (peterWeylFn γ z) * f (w, z) ∂haarPi ↥Bᶜ
            ∂haarPi ↥B ∂haarPi ↥B := by
      rw [← integral_star_peterWeylFn_mul]
      refine integral_congr_ae ?_
      filter_upwards [hI (toHaarL2 (partialCoeff B γ F))] with v hv
      rw [hv, Schatten.kernelApply]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [coeFn_toHaarL2 hpc] with w hw
      rw [hw]
      rfl
    have e₂ : (inner ℂ (peterWeylVec (glue B α γ))
        (toHaarL2 fun u : J → specialUnitary => G (restrictTo B u, restrictTo Bᶜ u)) : ℂ) =
        ∫ p, star (peterWeylFn α p.1) * star (peterWeylFn γ p.2) * G p
          ∂((haarPi ↥B).prod (haarPi ↥Bᶜ)) := by
      have hm : AEStronglyMeasurable (fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) =>
          star (peterWeylFn α p.1) * star (peterWeylFn γ p.2) * G p)
          (Measure.map (fun u : J → specialUnitary => (restrictTo B u, restrictTo Bᶜ u))
            (haarPi J)) :=
        (((ha.comp_measurable measurable_fst).mul
          (hc.comp_measurable measurable_snd)).mul hGm).aestronglyMeasurable
      rw [← integral_star_peterWeylFn_mul, ← hsplit.map_eq,
        integral_map hsplit.measurable.aemeasurable hm]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_toHaarL2 hGJ] with u hu
      rw [hu, peterWeylFn_glue, tensorFn, star_mul']
    rw [inner_peterWeylVec_tensorOne hT hS hP hB hB' X F α γ, e₁, e₂]
    exact (integral_mul_kernelSlice hKm (norm_nonneg K) hC hfm hf2 ha hc hA hA').symm
  have key : tensorOne B X F =
      toHaarL2 fun u : J → specialUnitary => G (restrictTo B u, restrictTo Bᶜ u) := by
    refine ext_inner_peterWeylVec hD fun β => ?_
    have hβ : glue B (restrictTo B β) (restrictTo Bᶜ β) = β :=
      (splitEquiv (X := PeterWeylLabel) B).left_inv β
    rw [← hβ]
    exact hcoef _ _
  rw [key]
  exact coeFn_toHaarL2 hGJ
theorem continuous_integral_kernel_glue (K : C((↥B → specialUnitary) × (↥B → specialUnitary), ℂ))
    (F : C(J → specialUnitary, ℂ)) :
    Continuous fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) =>
      ∫ w, K (p.1, w) * F (glue B w p.2) ∂haarPi ↥B := by
  have h' : Continuous fun q : ((↥B → specialUnitary) × (↥Bᶜ → specialUnitary)) ×
      (↥B → specialUnitary) => K (q.1.1, q.2) * F (glue B q.2 q.1.2) := by
    have h₁ : Continuous fun q : ((↥B → specialUnitary) × (↥Bᶜ → specialUnitary)) ×
        (↥B → specialUnitary) => (q.2, q.1.2) :=
      continuous_snd.prodMk (continuous_snd.comp continuous_fst)
    have h₃ := (continuous_glue (B := B)).comp h₁
    have h₂ : Continuous fun q : ((↥B → specialUnitary) × (↥Bᶜ → specialUnitary)) ×
        (↥B → specialUnitary) => (q.1.1, q.2) :=
      (continuous_fst.comp continuous_fst).prodMk continuous_snd
    exact (K.continuous.comp h₂).mul (F.continuous.comp h₃)
  have h : Continuous (Function.uncurry fun (p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary))
      (w : ↥B → specialUnitary) => K (p.1, w) * F (glue B w p.2)) := h'
  have h₂ := continuous_parametric_integral_of_continuous (μ := haarPi ↥B) h isCompact_univ
  simpa only [Measure.restrict_univ] using h₂
end
open SeveralVariables
theorem tensorOneKernelOpForAll_holds (hJ : GlueMeasurePreserving)
    (hT : TensorFnMemL2Inner)
    (hS : TensorOneSeriesConvergesForAll)
    (hD : AllOpsDeterminedByEntries)
    (hP : PeterWeylOrthonormalAndKernel)
    (hK : TransferOperators.GibbsHaarKernels.Statement) :
    TensorOneKernelOpForAll := by
  intro J _ _ B hB hB' X K hX
  exact ⟨fun F => tensorOne_ae_eq_integral hJ hT hS hD hP hK hB hB' X K hX F,
    fun F => continuous_integral_kernel_glue K F⟩
end YangMills.Construction.SpinHarmonics.TensorOneKernelOpProof
end
