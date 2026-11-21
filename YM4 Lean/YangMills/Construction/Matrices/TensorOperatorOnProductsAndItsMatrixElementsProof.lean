import YangMills.Construction.Matrices.ExpansionInThePeterWeylBasis
import YangMills.Construction.Matrices.TensorOperatorOfAnIntegralOperatorProof
import YangMills.Construction.Matrices.TensorOperatorOnProductsAndItsMatrixElements
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics.TensorOneProducts
section Classes
variable {I : Type} [Countable I]
theorem toHaarL2_congr {f g : (I → specialUnitary) → ℂ} (hfg : f =ᵐ[haarPi I] g) :
    toHaarL2 f = toHaarL2 g := by apply _root_.YangMills.Construction.SpinHarmonics.TensorOneKernelOpProof.toHaarL2_congr_ae <;> assumption
theorem toHaarL2_coe (φ : HaarL2 I) : toHaarL2 (φ : (I → specialUnitary) → ℂ) = φ := by apply _root_.YangMills.Construction.SpinHarmonics.TensorOneKernelOpProof.toHaarL2_coeFn <;> assumption
theorem toHaarL2_of_ae {g : (I → specialUnitary) → ℂ} (φ : HaarL2 I)
    (hg : g =ᵐ[haarPi I] φ) : toHaarL2 g = φ :=
  (toHaarL2_congr hg).trans (toHaarL2_coe φ)
theorem coe_toHaarL2 {f : (I → specialUnitary) → ℂ} (hf : MemLp f 2 (haarPi I)) :
    (toHaarL2 f : (I → specialUnitary) → ℂ) =ᵐ[haarPi I] f := by apply _root_.YangMills.Construction.SpinHarmonics.TensorOneKernelOpProof.coeFn_toHaarL2 <;> assumption
end Classes
section Part
variable {J : Type} [Finite J] (B : Set J)
theorem measurePreserving_restrictTo (hglue : GlueMeasurePreserving) :
    MeasurePreserving (restrictTo B : (J → specialUnitary) → ↥B → specialUnitary) (haarPi J)
      (haarPi ↥B) := by
  refine ⟨measurable_pi_lambda _ fun b => measurable_pi_apply _, ?_⟩
  have hm : Measurable (restrictTo B : (J → specialUnitary) → ↥B → specialUnitary) :=
    measurable_pi_lambda _ fun b => measurable_pi_apply _
  rw [← (hglue J B).map_eq, Measure.map_map hm (hglue J B).measurable]
  have hcomp : (restrictTo B : (J → specialUnitary) → ↥B → specialUnitary) ∘
      (fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2) = Prod.fst := by
    funext p
    exact congrArg Prod.fst ((splitEquiv (X := specialUnitary) B).right_inv p)
  rw [hcomp, Measure.map_fst_prod]
  simp
theorem measurePreserving_restrictTo_compl (hglue : GlueMeasurePreserving) :
    MeasurePreserving (restrictTo Bᶜ : (J → specialUnitary) → ↥Bᶜ → specialUnitary) (haarPi J)
      (haarPi ↥Bᶜ) := by
  refine ⟨measurable_pi_lambda _ fun b => measurable_pi_apply _, ?_⟩
  have hm : Measurable (restrictTo Bᶜ : (J → specialUnitary) → ↥Bᶜ → specialUnitary) :=
    measurable_pi_lambda _ fun b => measurable_pi_apply _
  rw [← (hglue J B).map_eq, Measure.map_map hm (hglue J B).measurable]
  have hcomp : (restrictTo Bᶜ : (J → specialUnitary) → ↥Bᶜ → specialUnitary) ∘
      (fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2) = Prod.snd := by
    funext p
    exact congrArg Prod.snd ((splitEquiv (X := specialUnitary) B).right_inv p)
  rw [hcomp, Measure.map_snd_prod]
  simp
variable {B}
theorem tensorFn_congr (hglue : GlueMeasurePreserving)
    {f f' : (↥B → specialUnitary) → ℂ} {h h' : (↥Bᶜ → specialUnitary) → ℂ}
    (hf : f =ᵐ[haarPi ↥B] f') (hh : h =ᵐ[haarPi ↥Bᶜ] h') :
    tensorFn B f h =ᵐ[haarPi J] tensorFn B f' h' := by
  have h₁ := (measurePreserving_restrictTo B hglue).quasiMeasurePreserving.ae_eq_comp hf
  have h₂ := (measurePreserving_restrictTo_compl B hglue).quasiMeasurePreserving.ae_eq_comp hh
  filter_upwards [h₁, h₂] with u e₁ e₂
  simp only [Function.comp_apply] at e₁ e₂
  simp only [tensorFn, e₁, e₂]
theorem partialCoeff_of_tensorFn (hglue : GlueMeasurePreserving) (F : HaarL2 J)
    {f : (↥B → specialUnitary) → ℂ} {h : (↥Bᶜ → specialUnitary) → ℂ}
    (hF : F =ᵐ[haarPi J] tensorFn B f h) (γ : PeterWeylIndex ↥Bᶜ) :
    partialCoeff B γ F =ᵐ[haarPi ↥B] fun v =>
      (∫ z, star (peterWeylFn γ z) * h z ∂haarPi ↥Bᶜ) * f v := by
  have h₁ : ∀ᵐ p ∂((haarPi ↥B).prod (haarPi ↥Bᶜ)),
      F (glue B p.1 p.2) = tensorFn B f h (glue B p.1 p.2) :=
    (hglue J B).quasiMeasurePreserving.ae_eq_comp hF
  filter_upwards [Measure.ae_ae_of_ae_prod h₁] with v hv
  unfold partialCoeff
  have h₂ : ∫ z, star (peterWeylFn γ z) * F (glue B v z) ∂haarPi ↥Bᶜ =
      ∫ z, f v * (star (peterWeylFn γ z) * h z) ∂haarPi ↥Bᶜ := by
    refine integral_congr_ae ?_
    filter_upwards [hv] with z hz
    rw [hz, tensorFn_glue]
    ring
  rw [h₂, integral_const_mul]
  ring
omit [Finite J] in
theorem integral_star_peterWeylFn_mul {I : Type} [Finite I] (γ : PeterWeylIndex I)
    (ω : HaarL2 I) :
    ∫ z, star (peterWeylFn γ z) * ω z ∂haarPi I = inner ℂ (peterWeylVec γ) ω := by apply _root_.YangMills.Construction.SpinHarmonics.TensorOneKernelOpProof.integral_star_peterWeylFn_mul <;> assumption
theorem exists_tensorFnLeft (hglue : GlueMeasurePreserving) (hmul : TensorFnMemL2Inner)
    (a : HaarL2 ↥B) :
    ∃ T : HaarL2 ↥Bᶜ →L[ℂ] HaarL2 J, ∀ ω, T ω = toHaarL2 (tensorFn B a ω) := by
  have hmem : ∀ ω : HaarL2 ↥Bᶜ, MemLp (tensorFn B a ω) 2 (haarPi J) :=
    fun ω => (hmul J B a a ω ω (Lp.memLp a) (Lp.memLp a) (Lp.memLp ω) (Lp.memLp ω)).1
  let L : HaarL2 ↥Bᶜ →ₗ[ℂ] HaarL2 J :=
    { toFun := fun ω => toHaarL2 (tensorFn B a ω)
      map_add' := by
        intro ω ω'
        refine toHaarL2_of_ae _ ?_
        refine (tensorFn_congr hglue (Filter.EventuallyEq.refl _ _)
          (Lp.coeFn_add ω ω')).trans ?_
        filter_upwards [Lp.coeFn_add (toHaarL2 (tensorFn B a ω))
          (toHaarL2 (tensorFn B a ω')), coe_toHaarL2 (hmem ω),
          coe_toHaarL2 (hmem ω')] with u h₁ h₂ h₃
        rw [h₁, Pi.add_apply, h₂, h₃]
        simp only [tensorFn, Pi.add_apply, mul_add]
      map_smul' := by
        intro c ω
        refine toHaarL2_of_ae _ ?_
        refine (tensorFn_congr hglue (Filter.EventuallyEq.refl _ _)
          (Lp.coeFn_smul c ω)).trans ?_
        filter_upwards [Lp.coeFn_smul c (toHaarL2 (tensorFn B a ω)),
          coe_toHaarL2 (hmem ω)] with u h₁ h₂
        rw [RingHom.id_apply, h₁, Pi.smul_apply, h₂]
        simp only [tensorFn, Pi.smul_apply, smul_eq_mul]
        ring }
  refine ⟨L.mkContinuous ‖a‖ ?_, fun ω => rfl⟩
  intro ω
  have h := (hmul J B a a ω ω (Lp.memLp a) (Lp.memLp a) (Lp.memLp ω) (Lp.memLp ω)).2
  rw [toHaarL2_coe, toHaarL2_coe, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖L ω‖ ^ 2 = (‖a‖ * ‖ω‖) ^ 2 := by
    rw [mul_pow]
    exact_mod_cast h
  exact le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h')
theorem tensorOne_tensorFn [Nonempty J] (hglue : GlueMeasurePreserving)
    (hmul : TensorFnMemL2Inner) (hser : TensorOneSeriesConvergesForAll)
    (hexp : PeterWeylExpansionHolds) (hB : B.Nonempty) (hB' : B ≠ Set.univ)
    (X : HaarL2 ↥B →L[ℂ] HaarL2 ↥B) (φ : HaarL2 ↥B) (ω : HaarL2 ↥Bᶜ) :
    tensorOne B X (toHaarL2 (tensorFn B φ ω)) = toHaarL2 (tensorFn B (X φ) ω) := by
  obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem B).1 hB'
  have : Nonempty ↥Bᶜ := ⟨⟨b, hb⟩⟩
  have hmem : MemLp (tensorFn B φ ω) 2 (haarPi J) :=
    (hmul J B φ φ ω ω (Lp.memLp φ) (Lp.memLp φ) (Lp.memLp ω) (Lp.memLp ω)).1
  set F : HaarL2 J := toHaarL2 (tensorFn B φ ω) with hFdef
  have hF : F =ᵐ[haarPi J] tensorFn B φ ω := coe_toHaarL2 hmem
  obtain ⟨T, hTω⟩ := exists_tensorFnLeft hglue hmul (X φ)
  have hsum := ((hexp ↥Bᶜ ω).1).mapL T
  have hterm : ∀ γ : PeterWeylIndex ↥Bᶜ,
      T ((inner ℂ (peterWeylVec γ) ω : ℂ) • peterWeylVec γ) = tensorSeriesTerm B X F γ := by
    intro γ
    have hcoef : toHaarL2 (partialCoeff B γ F) = (inner ℂ (peterWeylVec γ) ω : ℂ) • φ := by
      refine toHaarL2_of_ae _ ?_
      refine (partialCoeff_of_tensorFn hglue F hF γ).trans ?_
      filter_upwards [Lp.coeFn_smul (inner ℂ (peterWeylVec γ) ω : ℂ) φ] with v hv
      rw [hv, integral_star_peterWeylFn_mul, Pi.smul_apply, smul_eq_mul]
    rw [hTω, tensorSeriesTerm, hcoef, map_smul]
    refine toHaarL2_congr ?_
    have h₁ := tensorFn_congr (J := J) (B := B) hglue
      (Filter.EventuallyEq.refl _ (X φ : (↥B → specialUnitary) → ℂ))
      (Lp.coeFn_smul (inner ℂ (peterWeylVec γ) ω : ℂ) (peterWeylVec γ))
    have h₂ := tensorFn_congr (J := J) (B := B) hglue
      (Lp.coeFn_smul (inner ℂ (peterWeylVec γ) ω : ℂ) (X φ))
      (Filter.EventuallyEq.refl _ (peterWeylFn γ : (↥Bᶜ → specialUnitary) → ℂ))
    have h₃ := tensorFn_congr (J := J) (B := B) hglue
      (Filter.EventuallyEq.refl _ (X φ : (↥B → specialUnitary) → ℂ))
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := haarPi ↥Bᶜ) (peterWeylFn γ))
    filter_upwards [h₁, h₂, h₃] with u e₁ e₂ e₃
    rw [e₁, e₂]
    simp only [tensorFn, Pi.smul_apply, smul_eq_mul] at e₃ ⊢
    have e₃' : (X φ) (restrictTo B u) * (peterWeylVec γ) (restrictTo Bᶜ u) =
        (X φ) (restrictTo B u) * (peterWeylFn γ) (restrictTo Bᶜ u) := e₃
    calc _ = inner ℂ (peterWeylVec γ) ω *
          ((X φ) (restrictTo B u) * (peterWeylVec γ) (restrictTo Bᶜ u)) := by ring
      _ = _ := by rw [e₃']; ring
  have hnot : ¬ ∀ b, b ∈ B := fun h => hb (h b)
  rw [(hser J B hB hB' X).1 F |>.2.2, tensorOneApply, dif_neg hnot, ← hTω]
  have hsum' : HasSum (fun γ => tensorSeriesTerm B X F γ) (T ω) := by
    simpa only [Function.comp_def, hterm] using hsum
  exact hsum'.tsum_eq
end Part
theorem tensorOneOnProductsForAll_holds (hglue : GlueMeasurePreserving)
    (hmul : TensorFnMemL2Inner) (hser : TensorOneSeriesConvergesForAll)
    (hexp : PeterWeylExpansionHolds) (horth : PeterWeylOrthonormalAndKernel) :
    TensorOneOnProductsForAll := by
  intro J _ _ B hB hB' X
  obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem B).1 hB'
  have : Nonempty ↥Bᶜ := ⟨⟨b, hb⟩⟩
  have hglueVec : ∀ (α : PeterWeylIndex ↥B) (γ : PeterWeylIndex ↥Bᶜ),
      peterWeylVec (glue B α γ) = toHaarL2 (tensorFn B (peterWeylVec α) (peterWeylVec γ)) := by
    intro α γ
    refine (toHaarL2_of_ae _ ?_).symm
    refine (tensorFn_congr hglue
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := haarPi ↥B) (peterWeylFn α))
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := haarPi ↥Bᶜ)
        (peterWeylFn γ))).trans ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := haarPi J)
      (peterWeylFn (glue B α γ))] with u hu
    have hu' : peterWeylVec (glue B α γ) u = peterWeylFn (glue B α γ) u := hu
    rw [hu', peterWeylFn_glue]
  refine ⟨fun φ ω => ⟨(hmul J B φ φ ω ω (Lp.memLp φ) (Lp.memLp φ) (Lp.memLp ω) (Lp.memLp ω)).1,
    tensorOne_tensorFn hglue hmul hser hexp hB hB' X φ ω⟩, fun α α' γ γ' => ?_⟩
  have hort : Orthonormal ℂ (peterWeylVec : PeterWeylIndex ↥Bᶜ → HaarL2 ↥Bᶜ) :=
    (horth ↥Bᶜ fun _ => ⟨0⟩).1
  unfold peterWeylEntry
  rw [hglueVec α' γ', tensorOne_tensorFn hglue hmul hser hexp hB hB' X, hglueVec α γ]
  have h := (hmul J B (peterWeylVec α) (X (peterWeylVec α')) (peterWeylVec γ)
    (peterWeylVec γ') (Lp.memLp _) (Lp.memLp _) (Lp.memLp _) (Lp.memLp _)).2
  rw [toHaarL2_coe, toHaarL2_coe, toHaarL2_coe, toHaarL2_coe] at h
  rw [h]
  congr 1
  by_cases hγ : γ = γ'
  · subst hγ
    rw [if_pos rfl, inner_self_eq_norm_sq_to_K, hort.1]
    simp
  · rw [if_neg hγ]
    exact hort.2 hγ
end YangMills.Construction.SpinHarmonics.TensorOneProducts
end
