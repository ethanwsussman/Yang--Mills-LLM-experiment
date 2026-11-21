import YangMills.Construction.HilbertSpaces.PositiveSpectralMeasureOfAVectorProof
import YangMills.Construction.SpectralCalculus.SpectralIntegralConstruction
import YangMills.Construction.SpectralMeasures.ComplexMeasureUnseenByContinuousFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section
namespace YangMills.Construction.TwoPoints.SpectralMeasureUniqueness
open YangMills.Construction.SpectralCalculus (SpectralPlane spectralCharacter mulPairing)
open YangMills.Construction.TwoPoints.LineTransforms
  (UnitStrip spectralToStrip intervalRpow stripC0 stripSup stripAlgebra dyadics c1Functions)
section Parts
variable {X : Type} [MeasurableSpace X]
theorem isFiniteMeasure_variation (s : SignedMeasure X) : IsFiniteMeasure s.variation := by
  rw [← SignedMeasure.totalVariation_eq_variation]
  infer_instance
theorem integrable_of_norm_le {m : Measure X} [IsFiniteMeasure m] {f : X → ℂ} {C : ℝ}
    (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ C) : Integrable f m :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hb)
theorem integral_congr_of_transpose_eq {E F F' G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : VectorMeasure X F} {ν : VectorMeasure X F'}
    {B : E →L[ℝ] F →L[ℝ] G} {B' : E →L[ℝ] F' →L[ℝ] G} {f : X → E}
    (h : μ.transpose B = ν.transpose B') (hμ : μ.Integrable f) (hν : ν.Integrable f) :
    μ.integral f B = ν.integral f B' := by
  rw [VectorMeasure.integral_eq_setToFun_transpose hμ,
    VectorMeasure.integral_eq_setToFun_transpose hν]
  generalize_proofs p p'
  revert p p'
  rw [h]
  intros
  rfl
def ofSignedSmul (s : SignedMeasure X) (w : ℂ) : ComplexMeasure X :=
  s.mapRange (ContinuousLinearMap.toSpanSingleton ℝ w).toLinearMap.toAddMonoidHom
    (ContinuousLinearMap.toSpanSingleton ℝ w).continuous
theorem ofSignedSmul_apply (s : SignedMeasure X) (w : ℂ) (A : Set X) :
    ofSignedSmul s w A = (s A : ℝ) • w := rfl
theorem integral_ofSignedSmul (s : SignedMeasure X) (w : ℂ) {f : X → ℂ} {C : ℝ}
    (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ C) :
    (ofSignedSmul s w).integral f mulPairing =
      s.integral (fun x => w * f x) (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
  have := isFiniteMeasure_variation s
  have hs : Integrable f s.variation := integrable_of_norm_le hf hb
  have hc : Integrable f (ofSignedSmul s w).variation := integrable_of_norm_le hf hb
  let M : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ w
  have ht : (ofSignedSmul s w).transpose mulPairing =
      s.transpose ((ContinuousLinearMap.lsmul ℝ ℝ).flip ∘L M) := by
    ext A hA x
    change x * ((s A : ℝ) • w) = (s A : ℝ) • (w * x)
    rw [Complex.real_smul, Complex.real_smul]
    ring
  rw [integral_congr_of_transpose_eq ht hc hs]
  exact (VectorMeasure.integral_continuousLinearMap_comp (C := M) hs).symm
def jordanIntegral (s : SignedMeasure X) (f : X → ℂ) : ℂ :=
  ∫ x, f x ∂s.toJordanDecomposition.posPart - ∫ x, f x ∂s.toJordanDecomposition.negPart
theorem signedIntegral_eq_jordanIntegral (s : SignedMeasure X) {g : X → ℂ} {C : ℝ}
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) :
    s.integral g (ContinuousLinearMap.lsmul ℝ ℝ).flip = jordanIntegral s g := by
  have hP : (s.toJordanDecomposition.posPart.toSignedMeasure).Integrable g := by
    simpa [VectorMeasure.Integrable] using integrable_of_norm_le hg hb
  have hQ : (s.toJordanDecomposition.negPart.toSignedMeasure).Integrable g := by
    simpa [VectorMeasure.Integrable] using integrable_of_norm_le hg hb
  rw [jordanIntegral, ← VectorMeasure.integral_toSignedMeasure,
    ← VectorMeasure.integral_toSignedMeasure, ← VectorMeasure.integral_sub_vectorMeasure hP hQ]
  congr 1
  exact s.toSignedMeasure_toJordanDecomposition.symm
theorem eq_ofSignedSmul_re_add_im (c : ComplexMeasure X) :
    c = ofSignedSmul (ComplexMeasure.re c) 1 + ofSignedSmul (ComplexMeasure.im c) Complex.I := by
  ext A hA
  change c A = ofSignedSmul (ComplexMeasure.re c) 1 A +
    ofSignedSmul (ComplexMeasure.im c) Complex.I A
  rw [ofSignedSmul_apply, ofSignedSmul_apply]
  apply Complex.ext
  · simp
    rfl
  · simp
    rfl
theorem integral_eq_jordanIntegral (c : ComplexMeasure X) {f : X → ℂ} {C : ℝ}
    (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ C) :
    c.integral f mulPairing =
      jordanIntegral (ComplexMeasure.re c) f +
        Complex.I * jordanIntegral (ComplexMeasure.im c) f := by
  have hmI : Measurable fun x => Complex.I * f x := hf.const_mul _
  have hbI : ∀ x, ‖Complex.I * f x‖ ≤ C := fun x => by simpa using hb x
  have hm1 : Measurable fun x => (1 : ℂ) * f x := hf.const_mul _
  have hb1 : ∀ x, ‖(1 : ℂ) * f x‖ ≤ C := fun x => by simpa using hb x
  have i1 : (ofSignedSmul (ComplexMeasure.re c) 1).Integrable f := integrable_of_norm_le hf hb
  have i2 : (ofSignedSmul (ComplexMeasure.im c) Complex.I).Integrable f :=
    integrable_of_norm_le hf hb
  conv_lhs => rw [eq_ofSignedSmul_re_add_im c]
  rw [VectorMeasure.integral_add_vectorMeasure i1 i2, integral_ofSignedSmul _ _ hf hb,
    integral_ofSignedSmul _ _ hf hb, signedIntegral_eq_jordanIntegral _ hm1 hb1,
    signedIntegral_eq_jordanIntegral _ hmI hbI]
  simp only [jordanIntegral, one_mul, integral_const_mul]
  ring
theorem integral_const_mul_complex (c : ComplexMeasure X) (w : ℂ) {f : X → ℂ} {C : ℝ}
    (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ C) :
    c.integral (fun x => w * f x) mulPairing = w * c.integral f mulPairing := by
  have hbw : ∀ x, ‖w * f x‖ ≤ ‖w‖ * C := fun x => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg w)
  rw [integral_eq_jordanIntegral c (hf.const_mul w) hbw, integral_eq_jordanIntegral c hf hb]
  simp only [jordanIntegral, integral_const_mul]
  ring
end Parts
section Fubini
theorem norm_spectralCharacter_le_one (t : ℝ≥0) (s : ℝ) (p : SpectralPlane) :
    ‖spectralCharacter t s p‖ ≤ 1 := by apply _root_.YangMills.Construction.SpectralCalculus.SpectralIntegralConstruction.norm_spectralCharacter_le <;> assumption
theorem continuous_spectralCharacter (t : ℝ≥0) :
    Continuous fun x : ℝ × SpectralPlane => spectralCharacter t x.1 x.2 := by
  unfold spectralCharacter
  fun_prop
theorem continuous_spectralToStrip : Continuous spectralToStrip := by apply _root_.YangMills.Construction.TwoPoints.LineTransforms.VectorMeasure.continuous_spectralToStrip <;> assumption
theorem intervalRpow_mul_lineTransform_eq (t : ℝ≥0) (g : ℝ → ℂ) (p : SpectralPlane) :
    (intervalRpow t (spectralToStrip p).1 : ℂ) *
        YangMills.Construction.TwoPoints.LineTransforms.lineTransform g (spectralToStrip p).2 =
      ∫ s, g s * spectralCharacter t s p := by
  have hp : intervalRpow t (spectralToStrip p).1 = Real.exp (-(t : ℝ) * (p.1 : ℝ)) := by
    change Real.exp (-(p.1 : ℝ)) ^ (t : ℝ) = _
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hp]
  change ((Real.exp (-(t : ℝ) * (p.1 : ℝ)) : ℝ) : ℂ) *
    (∫ s : ℝ, g s * Complex.exp (Complex.I * (s : ℂ) * (p.2 : ℂ))) = _
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [spectralCharacter]
  rw [Complex.exp_add, Complex.ofReal_exp]
  push_cast
  ring_nf
theorem fubini_finiteMeasure (m : Measure SpectralPlane) [IsFiniteMeasure m] {g : ℝ → ℂ}
    (hgc : Continuous g) (hgi : Integrable g) (t : ℝ≥0) :
    Integrable (fun s => g s * ∫ p, spectralCharacter t s p ∂m) ∧
    ∫ p, (∫ s, g s * spectralCharacter t s p) ∂m =
      ∫ s, g s * ∫ p, spectralCharacter t s p ∂m := by
  have hK : Integrable (Function.uncurry fun (s : ℝ) (p : SpectralPlane) =>
      g s * spectralCharacter t s p) (volume.prod m) := by
    have hbound : Integrable (fun x : ℝ × SpectralPlane => ‖g x.1‖ * (1 : ℝ))
        (volume.prod m) := hgi.norm.mul_prod (integrable_const (1 : ℝ))
    refine hbound.mono' ?_ (ae_of_all _ fun x => ?_)
    · exact ((hgc.comp continuous_fst).mul (continuous_spectralCharacter t)).aestronglyMeasurable
    · change ‖g x.1 * spectralCharacter t x.1 x.2‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_spectralCharacter_le_one t x.1 x.2) (norm_nonneg _)
  have hpull : ∀ s, ∫ p, g s * spectralCharacter t s p ∂m =
      g s * ∫ p, spectralCharacter t s p ∂m := fun s => integral_const_mul _ _
  constructor
  · have := hK.integral_prod_left
    simpa only [Function.uncurry_apply_pair, hpull] using this
  · rw [← integral_integral_swap hK]
    simp only [hpull]
theorem integral_eq_zero_of_generator (μ : ComplexMeasure SpectralPlane) (t : ℝ≥0)
    (hz : ∀ s : ℝ, SpectralCalculus.laplaceFourier μ t s = 0) {g : ℝ → ℂ} (hgc : Continuous g)
    (hgi : Integrable g) {f : SpectralPlane → ℂ} {C : ℝ} (hf : Measurable f)
    (hb : ∀ p, ‖f p‖ ≤ C) (hfg : ∀ p, f p = ∫ s, g s * spectralCharacter t s p) :
    μ.integral f mulPairing = 0 := by
  have hfun : f = fun p => ∫ s, g s * spectralCharacter t s p := funext hfg
  let P₁ := (ComplexMeasure.re μ).toJordanDecomposition.posPart
  let P₂ := (ComplexMeasure.re μ).toJordanDecomposition.negPart
  let P₃ := (ComplexMeasure.im μ).toJordanDecomposition.posPart
  let P₄ := (ComplexMeasure.im μ).toJordanDecomposition.negPart
  obtain ⟨i₁, e₁⟩ := fubini_finiteMeasure P₁ hgc hgi t
  obtain ⟨i₂, e₂⟩ := fubini_finiteMeasure P₂ hgc hgi t
  obtain ⟨i₃, e₃⟩ := fubini_finiteMeasure P₃ hgc hgi t
  obtain ⟨i₄, e₄⟩ := fubini_finiteMeasure P₄ hgc hgi t
  have hpoint : ∀ s : ℝ, (g s * ∫ p, spectralCharacter t s p ∂P₁ -
      g s * ∫ p, spectralCharacter t s p ∂P₂) +
      Complex.I * (g s * ∫ p, spectralCharacter t s p ∂P₃ -
        g s * ∫ p, spectralCharacter t s p ∂P₄) = 0 := fun s => by
    have hm : Measurable (spectralCharacter t s) :=
      ((continuous_spectralCharacter t).comp (Continuous.prodMk_right s)).measurable
    have h := integral_eq_jordanIntegral μ hm (norm_spectralCharacter_le_one t s)
    have h0 : μ.integral (spectralCharacter t s) mulPairing = 0 := hz s
    rw [h0] at h
    simp only [jordanIntegral] at h
    linear_combination (-g s) * h
  rw [integral_eq_jordanIntegral μ hf hb, hfun]
  simp only [jordanIntegral]
  change ((∫ p, (∫ s, g s * spectralCharacter t s p) ∂P₁) -
    ∫ p, (∫ s, g s * spectralCharacter t s p) ∂P₂) +
    Complex.I * ((∫ p, (∫ s, g s * spectralCharacter t s p) ∂P₃) -
      ∫ p, (∫ s, g s * spectralCharacter t s p) ∂P₄) = 0
  rw [e₁, e₂, e₃, e₄, ← integral_sub i₁ i₂, ← integral_sub i₃ i₄, ← integral_const_mul]
  refine (integral_add (i₁.sub i₂) ((i₃.sub i₄).const_mul Complex.I)).symm.trans ?_
  simp only [Pi.sub_apply, hpoint, integral_zero]
end Fubini
section Density
theorem exists_bound_of_mem_stripC0 {F : UnitStrip → ℂ} (hF : F ∈ stripC0) :
    ∃ C : ℝ, ∀ y, ‖F y‖ ≤ C := by
  obtain ⟨hc, ht⟩ := hF
  have hev := (tendsto_order.1 ht).2 1 zero_lt_one
  rw [eventually_comap, eventually_atTop] at hev
  obtain ⟨R, hR⟩ := hev
  have hK : IsCompact ((Set.univ : Set unitInterval) ×ˢ Set.Icc (-R) R) :=
    isCompact_univ.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1, fun y => ?_⟩
  obtain ⟨a, q⟩ := y
  by_cases hq : R ≤ |q|
  · have h1 : stripSup F q < 1 := hR |q| hq q rfl
    have h2 : ‖F (a, q)‖ₑ < 1 :=
      lt_of_le_of_lt (le_iSup (fun a : unitInterval => ‖F (a, q)‖ₑ) a) h1
    rw [← ofReal_norm, ENNReal.ofReal_lt_one] at h2
    exact h2.le.trans (le_max_right _ _)
  · have hq' := abs_lt.1 (not_le.1 hq)
    exact (hC _ ⟨Set.mem_univ _, hq'.1.le, hq'.2.le⟩).trans (le_max_left _ _)
theorem measurable_comp_spectralToStrip {F : UnitStrip → ℂ} (hF : F ∈ stripC0) :
    Measurable (F ∘ spectralToStrip) :=
  (hF.1.comp continuous_spectralToStrip).measurable
theorem integrable_comp_spectralToStrip (μ : ComplexMeasure SpectralPlane) {F : UnitStrip → ℂ}
    (hF : F ∈ stripC0) : μ.Integrable (F ∘ spectralToStrip) := by
  obtain ⟨C, hC⟩ := exists_bound_of_mem_stripC0 hF
  exact integrable_of_norm_le (measurable_comp_spectralToStrip hF) fun p => hC _
theorem integral_eq_zero_of_mem_stripAlgebra (hle : stripAlgebra ≤ stripC0)
    (μ : ComplexMeasure SpectralPlane)
    (hz : ∀ t ∈ dyadics, ∀ s : ℝ, SpectralCalculus.laplaceFourier μ t s = 0)
    {F : UnitStrip → ℂ} (hF : F ∈ stripAlgebra) :
    μ.integral (F ∘ spectralToStrip) mulPairing = 0 := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨t, ht, g, hg, rfl⟩ := hG
    have hmem : (fun p : UnitStrip =>
        (intervalRpow t p.1 : ℂ) *
          YangMills.Construction.TwoPoints.LineTransforms.lineTransform g p.2) ∈ stripC0 :=
      hle (Submodule.subset_span ⟨t, ht, g, hg, rfl⟩)
    obtain ⟨C, hC⟩ := exists_bound_of_mem_stripC0 hmem
    have hgc : Continuous g := hg.1.continuous
    have hgi : Integrable g := hgc.integrable_of_hasCompactSupport hg.2.1
    exact integral_eq_zero_of_generator μ t (hz t ht) hgc hgi
      (measurable_comp_spectralToStrip hmem) (fun p => hC _)
      (fun p => intervalRpow_mul_lineTransform_eq t g p)
  | zero => exact VectorMeasure.integral_zero
  | add a b ha hb iha ihb =>
    have e := VectorMeasure.integral_fun_add (B := mulPairing)
      (integrable_comp_spectralToStrip μ (hle ha)) (integrable_comp_spectralToStrip μ (hle hb))
    change μ.integral (fun p => (a ∘ spectralToStrip) p + (b ∘ spectralToStrip) p) mulPairing = 0
    rw [e, iha, ihb, add_zero]
  | smul w a ha ih =>
    obtain ⟨C, hC⟩ := exists_bound_of_mem_stripC0 (hle ha)
    have e := integral_const_mul_complex μ w (measurable_comp_spectralToStrip (hle ha)) (C := C)
      (fun p => hC _)
    change μ.integral (fun p => w * (a ∘ spectralToStrip) p) mulPairing = 0
    rw [e, ih, mul_zero]
theorem integral_eq_zero_of_mem_stripC0 (hle : stripAlgebra ≤ stripC0)
    (hdense : LineTransforms.StripAlgebraDense)
    (μ : ComplexMeasure SpectralPlane)
    (hz : ∀ t ∈ dyadics, ∀ s : ℝ, SpectralCalculus.laplaceFourier μ t s = 0)
    {F : UnitStrip → ℂ} (hF : F ∈ stripC0) :
    μ.integral (F ∘ spectralToStrip) mulPairing = 0 := by
  obtain ⟨Fn, hFn, hlim⟩ := hdense F hF
  have key : ∀ n, ‖μ.integral (F ∘ spectralToStrip) mulPairing‖ ≤
      TestFunctions.uniformNorm (F - Fn n) * ‖mulPairing‖ *
        μ.variation.real Set.univ := fun n => by
    have hn := hle (hFn n)
    have hsub : F - Fn n ∈ stripC0 := Submodule.sub_mem _ hF hn
    obtain ⟨C, hC⟩ := exists_bound_of_mem_stripC0 hsub
    have hbdd : BddAbove (Set.range fun y => ‖(F - Fn n) y‖) :=
      ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩
    have e := VectorMeasure.integral_fun_sub (B := mulPairing)
      (integrable_comp_spectralToStrip μ hF) (integrable_comp_spectralToStrip μ hn)
    have h0 : μ.integral (Fn n ∘ spectralToStrip) mulPairing = 0 :=
      integral_eq_zero_of_mem_stripAlgebra hle μ hz (hFn n)
    rw [h0, sub_zero] at e
    rw [← e]
    refine VectorMeasure.norm_integral_le_of_norm_le_const (ae_of_all _ fun p => ?_)
    exact le_ciSup hbdd (spectralToStrip p)
  have hlim' := (hlim.mul_const ‖mulPairing‖).mul_const
    (μ.variation.real Set.univ)
  simp only [zero_mul] at hlim'
  exact norm_le_zero_iff.1 (ge_of_tendsto' hlim' key)
theorem restrict_mem_stripC0 {φ : ℝ × ℝ → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ) :
    (fun y : UnitStrip => ((φ ((y.1 : ℝ), y.2) : ℝ) : ℂ)) ∈ stripC0 := by
  refine ⟨by fun_prop, ?_⟩
  obtain ⟨r, hr⟩ := hs.isCompact.isBounded.subset_closedBall (0 : ℝ × ℝ)
  refine tendsto_const_nhds.congr' ?_
  rw [EventuallyEq, eventually_comap, eventually_atTop]
  refine ⟨r + 1, fun b hb q hq => ?_⟩
  refine (le_antisymm ?_ zero_le).symm
  refine iSup_le fun a => ?_
  have hout : ((a : ℝ), q) ∉ tsupport φ := fun hin => by
    have h1 := hr hin
    rw [mem_closedBall_zero_iff] at h1
    have h2 : |q| ≤ ‖((a : ℝ), q)‖ := by
      rw [Prod.norm_def]
      exact le_max_right _ _
    have h3 : r + 1 ≤ |q| := by rw [hq]; exact hb
    linarith
  simp [image_eq_zero_of_notMem_tsupport hout]
end Density
def expPlane (p : SpectralPlane) : ℝ × ℝ := (Real.exp (-(p.1 : ℝ)), p.2)
theorem continuous_expPlane : Continuous expPlane := by
  unfold expPlane
  fun_prop
theorem injective_expPlane : Function.Injective expPlane := by
  rintro ⟨E, q⟩ ⟨E', q'⟩ h
  have h1 : Real.exp (-(E : ℝ)) = Real.exp (-(E' : ℝ)) := congrArg Prod.fst h
  have h2 : q = q' := congrArg Prod.snd h
  have h3 : (E : ℝ) = E' := neg_injective (Real.exp_injective h1)
  rw [NNReal.coe_inj.1 h3, h2]
theorem eq_zero_of_laplaceFourier_eq_zero (hle : stripAlgebra ≤ stripC0)
    (hdense : LineTransforms.StripAlgebraDense)
    (hU : ComplexMeasureVanishing.Statement)
    (μ : ComplexMeasure SpectralPlane)
    (hz : ∀ t ∈ dyadics, ∀ s : ℝ, SpectralCalculus.laplaceFourier μ t s = 0) : μ = 0 := by
  have hU' : ∀ ν : ComplexMeasure (ℝ × ℝ), (∀ φ : ℝ × ℝ → ℝ, Continuous φ → HasCompactSupport φ →
      ν.integral (fun y => (φ y : ℂ)) mulPairing = 0) → ν = 0 :=
    fun ν h => hU .realReal ν h
  have hmeas : Measurable expPlane := continuous_expPlane.measurable
  have hν : μ.map expPlane = 0 := by
    refine hU' _ fun φ hc hs => ?_
    have hmem := restrict_mem_stripC0 hc hs
    have hzero := integral_eq_zero_of_mem_stripC0 hle hdense μ hz hmem
    have hint := integrable_comp_spectralToStrip μ hmem
    have hcont : Continuous fun y : ℝ × ℝ => ((φ y : ℝ) : ℂ) := by fun_prop
    rw [VectorMeasure.integral_map hmeas hcont.aestronglyMeasurable hint]
    exact hzero
  have hemb : MeasurableEmbedding expPlane := hmeas.measurableEmbedding injective_expPlane
  ext B hB
  have h1 := VectorMeasure.map_apply μ hmeas (hemb.measurableSet_image.2 hB)
  rw [Set.preimage_image_eq B injective_expPlane, hν] at h1
  exact h1.symm
theorem holds (hD : LineTransforms.ConvPowDensity.Statement)
    (hU : ComplexMeasureVanishing.Statement) : Statement := by
  obtain ⟨-, -, -, -, -, hA, hdense⟩ := hD
  have hle := hA.1
  refine ⟨fun μ hz => eq_zero_of_laplaceFourier_eq_zero hle hdense hU μ hz, fun μ ν h => ?_⟩
  have hd : μ - ν = 0 := by
    refine eq_zero_of_laplaceFourier_eq_zero hle hdense hU (μ - ν) fun t _ s => ?_
    have hm : Measurable (spectralCharacter t s) :=
      ((continuous_spectralCharacter t).comp (Continuous.prodMk_right s)).measurable
    have i1 : μ.Integrable (spectralCharacter t s) :=
      integrable_of_norm_le hm (norm_spectralCharacter_le_one t s)
    have i2 : ν.Integrable (spectralCharacter t s) :=
      integrable_of_norm_le hm (norm_spectralCharacter_le_one t s)
    have e : SpectralCalculus.laplaceFourier (μ - ν) t s =
        (μ - ν).integral (spectralCharacter t s) mulPairing := rfl
    rw [e, VectorMeasure.integral_sub_vectorMeasure i1 i2]
    exact sub_eq_zero.2 (h t s)
  exact sub_eq_zero.1 hd
end YangMills.Construction.TwoPoints.SpectralMeasureUniqueness
end
