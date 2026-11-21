import YangMills.Construction.Matrices.ExpansionInThePeterWeylBasis
import YangMills.Construction.Matrices.GluingFamiliesPreservesProductsOfHaarMeasuresForm
import YangMills.Construction.Matrices.PartialCoefficientsOfASquareIntegrableFunctionForm
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SpinHarmonics.PartialCoeffL2
theorem countable_peterWeylLabel : Countable PeterWeylLabel := by
  have hinj : Function.Injective
      (fun e : PeterWeylLabel => (e.1.doubled, (e.rowIdx : ℕ), (e.colIdx : ℕ))) := by
    rintro ⟨⟨n⟩, a, c⟩ ⟨⟨m⟩, a', c'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h₀, h₁, h₂⟩ := h
    subst h₀
    have ha : a = a' := Fin.ext h₁
    have hc : c = c' := Fin.ext h₂
    subst ha
    subst hc
    rfl
  exact hinj.countable
theorem lintegral_enorm_sq_eq_norm_sq {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    (g : Lp ℂ 2 μ) : ∫⁻ a, ‖g a‖ₑ ^ 2 ∂μ = ENNReal.ofReal (‖g‖ ^ 2) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := (g : α → ℂ)) (μ := μ) (p := 2) two_ne_zero
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  rw [← h, Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Lp.memLp g).2.ne]
theorem memLp_two_of_lintegral_enorm_sq_lt_top {α : Type*} {m0 : MeasurableSpace α}
    {μ : Measure α} {f : α → ℂ} (hf : AEStronglyMeasurable f μ)
    (h : ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ < ∞) : MemLp f 2 μ := by
  refine ⟨hf, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
    ENNReal.ofNat_ne_top).2 ?_⟩
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] using h
theorem toHaarL2_eq_toLp {ι : Type} [Countable ι] {f : (ι → specialUnitary) → ℂ}
    (h : MemLp f 2 (haarPi ι)) : toHaarL2 f = h.toLp f :=
  dif_pos h
theorem norm_toHaarL2_sq {ι : Type} [Countable ι] {f : (ι → specialUnitary) → ℂ}
    (h : MemLp f 2 (haarPi ι)) :
    ‖toHaarL2 f‖ ^ 2 = (∫⁻ a, ‖f a‖ₑ ^ 2 ∂haarPi ι).toReal := by
  have h₁ := lintegral_enorm_sq_eq_norm_sq (toHaarL2 f)
  have h₂ : ∫⁻ a, ‖toHaarL2 f a‖ₑ ^ 2 ∂haarPi ι = ∫⁻ a, ‖f a‖ₑ ^ 2 ∂haarPi ι := by
    rw [toHaarL2_eq_toLp h]
    exact lintegral_congr_ae (h.coeFn_toLp.mono fun a ha => by simp only [ha])
  rw [← h₂, h₁, ENNReal.toReal_ofReal (by positivity)]
section Slices
variable {ι : Type} [Finite ι] (B : Set ι)
theorem partialCoeff_eq_inner (γ : PeterWeylIndex ↥Bᶜ) (F : HaarL2 ι)
    (v : ↥B → specialUnitary) (hv : MemLp (fun z => F (glue B v z)) 2 (haarPi ↥Bᶜ)) :
    partialCoeff B γ F v = inner ℂ (peterWeylVec γ) (hv.toLp _) := by
  rw [L2.inner_def, partialCoeff]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) (haarPi ↥Bᶜ)
    (peterWeylFn γ), hv.coeFn_toLp] with z h₁ h₂
  rw [peterWeylVec, h₁, h₂, RCLike.inner_apply']
  rfl
theorem tsum_enorm_partialCoeff_sq (hE : SeveralVariables.PeterWeylExpansion ↥Bᶜ)
    (F : HaarL2 ι) (v : ↥B → specialUnitary)
    (hv : MemLp (fun z => F (glue B v z)) 2 (haarPi ↥Bᶜ)) :
    ∑' γ : PeterWeylIndex ↥Bᶜ, ‖partialCoeff B γ F v‖ₑ ^ 2 =
      ∫⁻ z, ‖F (glue B v z)‖ₑ ^ 2 ∂haarPi ↥Bᶜ := by
  have h := (hE (hv.toLp _)).2.2
  have key : ∀ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2 := fun x => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  calc ∑' γ : PeterWeylIndex ↥Bᶜ, ‖partialCoeff B γ F v‖ₑ ^ 2
      = ∑' γ : PeterWeylIndex ↥Bᶜ,
          ENNReal.ofReal (‖(inner ℂ (peterWeylVec γ) (hv.toLp _) : ℂ)‖ ^ 2) :=
        tsum_congr fun γ => by rw [key, partialCoeff_eq_inner B γ F v hv]
    _ = ENNReal.ofReal
          (∑' γ : PeterWeylIndex ↥Bᶜ, ‖(inner ℂ (peterWeylVec γ) (hv.toLp _) : ℂ)‖ ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h.summable).symm
    _ = ENNReal.ofReal (‖hv.toLp _‖ ^ 2) := by rw [h.tsum_eq]
    _ = ∫⁻ z, ‖hv.toLp _ z‖ₑ ^ 2 ∂haarPi ↥Bᶜ := (lintegral_enorm_sq_eq_norm_sq _).symm
    _ = ∫⁻ z, ‖F (glue B v z)‖ₑ ^ 2 ∂haarPi ↥Bᶜ :=
        lintegral_congr_ae (hv.coeFn_toLp.mono fun z hz => by simp only [hz])
variable (hJ : MeasurePreserving
  (fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2)
  ((haarPi ↥B).prod (haarPi ↥Bᶜ)) (haarPi ι))
include hJ
theorem lintegral_lintegral_glue (F : HaarL2 ι) :
    ∫⁻ v, ∫⁻ z, ‖F (glue B v z)‖ₑ ^ 2 ∂haarPi ↥Bᶜ ∂haarPi ↥B =
      ENNReal.ofReal (‖F‖ ^ 2) := by
  have hF : Measurable fun u => ‖F u‖ₑ ^ 2 :=
    (Lp.stronglyMeasurable F).measurable.enorm.pow_const 2
  rw [← lintegral_enorm_sq_eq_norm_sq F, ← hJ.lintegral_comp hF]
  exact (lintegral_prod _ (hF.comp hJ.measurable).aemeasurable).symm
theorem ae_memLp_slice (F : HaarL2 ι) :
    ∀ᵐ v ∂haarPi ↥B, MemLp (fun z => F (glue B v z)) 2 (haarPi ↥Bᶜ) := by
  have hF : Measurable fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) =>
      ‖F (glue B p.1 p.2)‖ₑ ^ 2 :=
    ((Lp.stronglyMeasurable F).measurable.enorm.pow_const 2).comp hJ.measurable
  have hm : AEMeasurable (fun v => ∫⁻ z, ‖F (glue B v z)‖ₑ ^ 2 ∂haarPi ↥Bᶜ)
      (haarPi ↥B) := (hF.lintegral_prod_right' (ν := haarPi ↥Bᶜ)).aemeasurable
  have hfin : ∫⁻ v, ∫⁻ z, ‖F (glue B v z)‖ₑ ^ 2 ∂haarPi ↥Bᶜ ∂haarPi ↥B ≠ ∞ := by
    rw [lintegral_lintegral_glue B hJ F]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top' hm hfin] with v hv
  refine memLp_two_of_lintegral_enorm_sq_lt_top ?_ hv
  exact ((Lp.stronglyMeasurable F).comp_measurable
    (hJ.measurable.comp measurable_prodMk_left)).aestronglyMeasurable
theorem aestronglyMeasurable_partialCoeff (γ : PeterWeylIndex ↥Bᶜ) (F : HaarL2 ι) :
    AEStronglyMeasurable (partialCoeff B γ F) (haarPi ↥B) := by
  have hm : Measurable fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) =>
      star (peterWeylFn γ p.2) * F (glue B p.1 p.2) :=
    ((continuous_star.comp (peterWeylFn γ).continuous).measurable.comp measurable_snd).mul
      ((Lp.stronglyMeasurable F).measurable.comp hJ.measurable)
  exact hm.aestronglyMeasurable.integral_prod_right'
theorem tsum_lintegral_partialCoeff (hE : SeveralVariables.PeterWeylExpansion ↥Bᶜ)
    (F : HaarL2 ι) :
    ∑' γ : PeterWeylIndex ↥Bᶜ, ∫⁻ v, ‖partialCoeff B γ F v‖ₑ ^ 2 ∂haarPi ↥B =
      ENNReal.ofReal (‖F‖ ^ 2) := by
  have := countable_peterWeylLabel
  rw [← lintegral_tsum fun γ =>
    (aestronglyMeasurable_partialCoeff B hJ γ F).enorm.pow_const 2, ←
    lintegral_lintegral_glue B hJ F]
  exact lintegral_congr_ae ((ae_memLp_slice B hJ F).mono fun v hv =>
    tsum_enorm_partialCoeff_sq B hE F v hv)
theorem memLp_partialCoeff (hE : SeveralVariables.PeterWeylExpansion ↥Bᶜ)
    (γ : PeterWeylIndex ↥Bᶜ) (F : HaarL2 ι) : MemLp (partialCoeff B γ F) 2 (haarPi ↥B) := by
  refine memLp_two_of_lintegral_enorm_sq_lt_top (aestronglyMeasurable_partialCoeff B hJ γ F) ?_
  calc ∫⁻ v, ‖partialCoeff B γ F v‖ₑ ^ 2 ∂haarPi ↥B
      ≤ ∑' γ : PeterWeylIndex ↥Bᶜ, ∫⁻ v, ‖partialCoeff B γ F v‖ₑ ^ 2 ∂haarPi ↥B :=
        ENNReal.le_tsum γ
    _ = ENNReal.ofReal (‖F‖ ^ 2) := tsum_lintegral_partialCoeff B hJ hE F
    _ < ∞ := ENNReal.ofReal_lt_top
theorem hasSum_norm_partialCoeff_sq (hE : SeveralVariables.PeterWeylExpansion ↥Bᶜ)
    (F : HaarL2 ι) :
    HasSum (fun γ : PeterWeylIndex ↥Bᶜ => ‖toHaarL2 (partialCoeff B γ F)‖ ^ 2) (‖F‖ ^ 2) := by
  have hs := tsum_lintegral_partialCoeff B hJ hE F
  have hfin : ∑' γ : PeterWeylIndex ↥Bᶜ,
      ∫⁻ v, ‖partialCoeff B γ F v‖ₑ ^ 2 ∂haarPi ↥B ≠ ∞ := by
    rw [hs]
    exact ENNReal.ofReal_ne_top
  have h := ENNReal.hasSum_toReal hfin
  rw [← ENNReal.tsum_toReal_eq (fun γ => ENNReal.ne_top_of_tsum_ne_top hfin γ), hs,
    ENNReal.toReal_ofReal (by positivity)] at h
  convert h using 2 with γ
  exact norm_toHaarL2_sq (memLp_partialCoeff B hJ hE γ F)
theorem partialCoeff_add (γ : PeterWeylIndex ↥Bᶜ) (F G : HaarL2 ι) :
    partialCoeff B γ (F + G) =ᵐ[haarPi ↥B] partialCoeff B γ F + partialCoeff B γ G := by
  have h : ∀ᵐ p ∂((haarPi ↥B).prod (haarPi ↥Bᶜ)),
      (F + G : HaarL2 ι) (glue B p.1 p.2) = F (glue B p.1 p.2) + G (glue B p.1 p.2) :=
    hJ.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_add F G)
  filter_upwards [ae_memLp_slice B hJ F, ae_memLp_slice B hJ G, ae_memLp_slice B hJ (F + G),
    Measure.ae_ae_of_ae_prod h] with v h₁ h₂ h₃ h₄
  rw [Pi.add_apply, partialCoeff_eq_inner B γ F v h₁, partialCoeff_eq_inner B γ G v h₂,
    partialCoeff_eq_inner B γ _ v h₃, ← inner_add_right, ← MemLp.toLp_add]
  congr 1
  exact MemLp.toLp_congr _ _ h₄
theorem partialCoeff_smul (γ : PeterWeylIndex ↥Bᶜ) (c : ℂ) (F : HaarL2 ι) :
    partialCoeff B γ (c • F) =ᵐ[haarPi ↥B] c • partialCoeff B γ F := by
  have h : ∀ᵐ p ∂((haarPi ↥B).prod (haarPi ↥Bᶜ)),
      (c • F : HaarL2 ι) (glue B p.1 p.2) = c • F (glue B p.1 p.2) :=
    hJ.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul c F)
  filter_upwards [ae_memLp_slice B hJ F, ae_memLp_slice B hJ (c • F),
    Measure.ae_ae_of_ae_prod h] with v h₁ h₂ h₃
  rw [Pi.smul_apply, partialCoeff_eq_inner B γ F v h₁,
    partialCoeff_eq_inner B γ _ v h₂, smul_eq_mul, ← inner_smul_right,
    ← MemLp.toLp_const_smul]
  congr 1
  exact MemLp.toLp_congr _ _ h₃
end Slices
theorem partialCoeffL2Properties_of (hE : PeterWeylExpansionHolds)
    (hJ : GlueMeasurePreserving) : PartialCoeffL2Properties := by
  intro ι _ _ B _ hB
  have : Nonempty ↥Bᶜ := (Set.nonempty_compl.mpr hB).to_subtype
  have hE' : SeveralVariables.PeterWeylExpansion ↥Bᶜ := hE ↥Bᶜ
  have hJ' := hJ ι B
  have hmem := fun γ F => memLp_partialCoeff B hJ' hE' γ F
  have hsum := hasSum_norm_partialCoeff_sq B hJ' hE'
  refine ⟨hmem, fun γ => ?_, hsum⟩
  refine ⟨LinearMap.mkContinuous
    { toFun := fun F => toHaarL2 (partialCoeff B γ F)
      map_add' := fun F G => ?_
      map_smul' := fun c F => ?_ } 1 fun F => ?_, fun F => rfl⟩
  · rw [toHaarL2_eq_toLp (hmem γ (F + G)), toHaarL2_eq_toLp (hmem γ F),
      toHaarL2_eq_toLp (hmem γ G), ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (partialCoeff_add B hJ' γ F G)
  · rw [RingHom.id_apply, toHaarL2_eq_toLp (hmem γ (c • F)), toHaarL2_eq_toLp (hmem γ F),
      ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (partialCoeff_smul B hJ' γ c F)
  · have h := le_hasSum (hsum F) γ fun _ _ => by positivity
    rw [one_mul]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
end YangMills.Construction.SpinHarmonics.PartialCoeffL2
end
