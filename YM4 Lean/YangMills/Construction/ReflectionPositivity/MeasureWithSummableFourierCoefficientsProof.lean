import YangMills.Construction.ReflectionPositivity.MeasureWithSummableFourierCoefficients
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Real
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.EnergyMomentum.FourierDensity
open YangMills.Construction.ReflectionPositivity.DirectionPictures
section Density
variable {T : Type*} [MetricSpace T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T]
theorem integrable_of_continuousMap (ρ : Measure T) [IsFiniteMeasure ρ] (f : C(T, ℂ)) :
    Integrable (fun x => f x) ρ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
def integralCLM (ρ : Measure T) [IsFiniteMeasure ρ] : C(T, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂ρ
      map_add' := fun f g =>
        integral_add (integrable_of_continuousMap ρ f) (integrable_of_continuousMap ρ g)
      map_smul' := fun c f => integral_smul c (fun x => f x) }
    (ρ.real univ)
    (fun f => by
      have hb := norm_integral_le_of_norm_le_const (μ := ρ) (f := fun x => f x) (C := ‖f‖)
        (ae_of_all _ fun x => f.norm_coe_le_norm x)
      simpa [mul_comm] using hb)
theorem eq_withDensity_of_integral_eq (M ν : Measure T) [IsFiniteMeasure M] [IsFiniteMeasure ν]
    [ν.IsOpenPosMeasure] (h : C(T, ℂ))
    (K : ∀ f : C(T, ℂ), ∫ x, f x ∂M = ∫ x, f x * h x ∂ν) :
    (∀ x, (h x).im = 0 ∧ 0 ≤ (h x).re) ∧
      M = ν.withDensity fun x => ENNReal.ofReal (h x).re := by
  have him : Continuous fun x => (h x).im := Complex.continuous_im.comp h.continuous
  have hre : Continuous fun x => (h x).re := Complex.continuous_re.comp h.continuous
  have test : ∀ g : T → ℝ, Continuous g →
      ∫ x, g x ∂M = ∫ x, g x * (h x).re ∂ν ∧ ∫ x, g x * (h x).im ∂ν = 0 := by
    intro g hg
    let f : C(T, ℂ) := ⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp hg⟩
    have e := K f
    have hi : Integrable (fun x => f x * h x) ν := integrable_of_continuousMap ν (f * h)
    have e1 : ∫ x, f x ∂M = ((∫ x, g x ∂M : ℝ) : ℂ) := integral_ofReal
    have e2 : ∫ x, g x * (h x).re ∂ν = (∫ x, f x * h x ∂ν).re := by
      have := Complex.reCLM.integral_comp_comm hi
      simpa [f] using this
    have e3 : ∫ x, g x * (h x).im ∂ν = (∫ x, f x * h x ∂ν).im := by
      have := Complex.imCLM.integral_comp_comm hi
      simpa [f] using this
    rw [e2, e3, ← e, e1]
    simp
  have zero_of_sq : ∀ g : T → ℝ, Continuous g → ∫ x, g x * g x ∂ν = 0 → ∀ x, g x = 0 := by
    intro g hg h0 x
    have hint : Integrable (fun x => g x * g x) ν :=
      (hg.mul hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (g x)) hint).mp h0
    have e := (Continuous.ae_eq_iff_eq ν (hg.mul hg) continuous_zero).mp hae
    exact mul_self_eq_zero.mp (congrFun e x)
  have h_im : ∀ x, (h x).im = 0 := zero_of_sq _ him (test _ him).2
  have h_re : ∀ x, 0 ≤ (h x).re := by
    let g : T → ℝ := fun x => max (-(h x).re) 0
    have hg : Continuous g := hre.neg.max continuous_const
    have hgn : ∀ x, 0 ≤ g x := fun x => le_max_right _ _
    have e2 : ∀ x, g x * (h x).re = -(g x * g x) := by
      intro x
      rcases le_total (-(h x).re) 0 with c | c
      · simp [g, max_eq_right c]
      · simp [g, max_eq_left c]
    have e1 := (test g hg).1
    simp_rw [e2] at e1
    rw [integral_neg] at e1
    have hM : 0 ≤ ∫ x, g x ∂M := integral_nonneg hgn
    have hν : 0 ≤ ∫ x, g x * g x ∂ν := integral_nonneg fun x => mul_self_nonneg (g x)
    have h0 : ∫ x, g x * g x ∂ν = 0 := by linarith
    intro x
    have := zero_of_sq g hg h0 x
    have h2 : -(h x).re ≤ g x := le_max_left _ _
    linarith
  refine ⟨fun x => ⟨h_im x, h_re x⟩, ?_⟩
  have hfin : IsFiniteMeasure (ν.withDensity fun x => ENNReal.ofReal (h x).re) :=
    isFiniteMeasure_withDensity_ofReal
      (hre.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).2
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [(test f f.continuous).1, integral_withDensity_eq_integral_toReal_smul
    hre.measurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [ENNReal.toReal_ofReal (h_re x), mul_comm]
end Density
variable {μ : Fin 4}
theorem fourier_coe_eq_exp (x : ℝ) (n : ℤ) :
    fourier n (x : AddCircle (2 * π)) = Complex.exp (Complex.I * ((x * n : ℝ) : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
theorem torusCharacter_eq_prod_fourier (w : orthLattice μ) (η : DualTorus μ) :
    torusCharacter μ w η = ∏ l, fourier ((w : Fin 4 → ℤ) l.1) (η l) := by
  have hη : ∀ l, η l = ((boxRep μ η l : ℝ) : AddCircle (2 * π)) :=
    fun l => (congrFun (torusProj_boxRep μ η) l).symm
  rw [torusCharacter, angleDot, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun l _ => ?_
  conv_rhs => rw [hη l, fourier_coe_eq_exp]
def charCM (w : orthLattice μ) : C(DualTorus μ, ℂ) where
  toFun := torusCharacter μ w
  continuous_toFun := by
    have hw : torusCharacter μ w = fun η => ∏ l, fourier ((w : Fin 4 → ℤ) l.1) (η l) :=
      funext (torusCharacter_eq_prod_fourier w)
    rw [hw]
    exact continuous_finsetProd _ fun l _ => (fourier _).continuous.comp (continuous_apply l)
theorem charCM_apply (w : orthLattice μ) (η : DualTorus μ) :
    charCM w η = torusCharacter μ w η := rfl
theorem charCM_add (v w : orthLattice μ) :
    charCM (v + w) = charCM v * charCM w := by
  ext η
  simp only [charCM_apply, ContinuousMap.mul_apply, torusCharacter_eq_prod_fourier,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  exact fourier_add
theorem charCM_zero : charCM (0 : orthLattice μ) = 1 := by
  ext η
  simp only [charCM_apply, torusCharacter_eq_prod_fourier, ContinuousMap.one_apply]
  exact Finset.prod_eq_one fun l _ => fourier_zero
theorem star_charCM (w : orthLattice μ) : star (charCM w) = charCM (-w) := by
  ext η
  simp only [ContinuousMap.star_apply, charCM_apply, torusCharacter_eq_prod_fourier, star_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  exact fourier_neg.symm
theorem norm_torusCharacter (w : orthLattice μ) (η : DualTorus μ) :
    ‖torusCharacter μ w η‖ = 1 := by
  rw [torusCharacter, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _
theorem torusFourierTerm_eq_mul_charCM (M : Measure (DualTorus μ)) (w : orthLattice μ)
    (η : DualTorus μ) :
    torusFourierTerm μ M w η = torusFourierCoeff μ M w * charCM (-w) η := by
  rw [torusFourierTerm, charCM_apply, torusCharacter]
  congr 2
  simp [angleDot]
def trigPoly (μ : Fin 4) : StarSubalgebra ℂ C(DualTorus μ, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range (charCM (μ := μ)))
  star_mem' := by
    change Algebra.adjoin ℂ (range (charCM (μ := μ))) ≤
      star (Algebra.adjoin ℂ (range (charCM (μ := μ))))
    refine Algebra.adjoin_le ?_
    rintro - ⟨w, rfl⟩
    refine Algebra.subset_adjoin ⟨-w, ?_⟩
    rw [← star_charCM]
theorem trigPoly_toSubmodule :
    Subalgebra.toSubmodule (trigPoly μ).toSubalgebra =
      Submodule.span ℂ (range (charCM (μ := μ))) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0, charCM_zero⟩ ?_ hx
  rintro - - - - ⟨m, rfl⟩ ⟨n, rfl⟩
  exact ⟨m + n, charCM_add m n⟩
theorem trigPoly_separatesPoints :
    (trigPoly μ).SeparatesPoints := by
  intro x y hxy
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hxy
  let w : orthLattice μ := ⟨Pi.single l.1 1, by
    rw [mem_orthLattice]
    exact Pi.single_eq_of_ne l.2.symm _⟩
  refine ⟨_, ⟨charCM w, Algebra.subset_adjoin ⟨w, rfl⟩, rfl⟩, ?_⟩
  have hval : ∀ z : DualTorus μ, charCM w z = fourier 1 (z l) := by
    intro z
    rw [charCM_apply, torusCharacter_eq_prod_fourier, Finset.prod_eq_single l]
    · simp [w]
    · intro b _ hb
      have hb' : b.1 ≠ l.1 := fun e => hb (Subtype.ext e)
      have : (w : Fin 4 → ℤ) b.1 = 0 := Pi.single_eq_of_ne hb' _
      rw [this]
      exact fourier_zero
    · simp
  simp only [hval, fourier_one]
  intro e
  exact hl (AddCircle.injective_toCircle Real.two_pi_pos.ne' (Circle.coe_injective e))
theorem dense_span_charCM :
    Dense (Submodule.span ℂ (range (charCM (μ := μ))) : Set C(DualTorus μ, ℂ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, ← trigPoly_toSubmodule]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
      trigPoly_separatesPoints)
instance torusMeasure_isFiniteMeasure (μ : Fin 4) : IsFiniteMeasure (torusMeasure μ) :=
  ⟨by rw [torusMeasure_univ]; exact ENNReal.ofReal_lt_top⟩
instance torusMeasure_isOpenPosMeasure (μ : Fin 4) : (torusMeasure μ).IsOpenPosMeasure := by
  refine ⟨fun U hU hne h0 => ?_⟩
  obtain ⟨η, hη⟩ := hne
  have hP : IsOpen (torusProj μ ⁻¹' U) := hU.preimage (continuous_torusProj μ)
  let B : Set (TransverseAxis μ → ℝ) := Set.pi univ fun _ => Ioo (-π) π
  have hB : IsOpen B := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have hBbox : B ⊆ fundamentalBox μ := fun x hx l => Ioo_subset_Ioc_self (hx l (mem_univ l))
  have hcl : boxRep μ η ∈ closure B := by
    rw [closure_pi_set]
    intro l _
    have hlt : -π < π := by linarith [Real.pi_pos]
    rw [closure_Ioo hlt.ne]
    exact Ioc_subset_Icc_self (boxRep_mem μ η l)
  have hx : boxRep μ η ∈ torusProj μ ⁻¹' U := by
    rw [mem_preimage, torusProj_boxRep]
    exact hη
  obtain ⟨y, hyP, hyB⟩ := mem_closure_iff.mp hcl _ hP hx
  have hpos : volume (torusProj μ ⁻¹' U ∩ B) ≠ 0 :=
    ((hP.inter hB).measure_pos volume ⟨y, hyP, hyB⟩).ne'
  rw [torusMeasure, Measure.map_apply (continuous_torusProj μ).measurable hU.measurableSet,
    Measure.restrict_apply hP.measurableSet] at h0
  exact hpos (measure_mono_null (inter_subset_inter_right _ hBbox) h0)
theorem torusMeasure_real_univ (μ : Fin 4) :
    (torusMeasure μ).real univ = (2 * π) ^ 3 := by
  rw [Measure.real, torusMeasure_univ, ENNReal.toReal_ofReal (by positivity)]
theorem integral_exp_int_mul_Ioc {n : ℤ} (hn : n ≠ 0) :
    ∫ x in Ioc (-π) π, Complex.exp (Complex.I * ((x * n : ℝ) : ℂ)) = 0 := by
  have hc : Complex.I * (n : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hn)
  have e : ∀ x : ℝ, Complex.exp (Complex.I * ((x * n : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) := fun x => by
    congr 1
    push_cast
    ring
  simp_rw [e]
  rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_exp_mul_complex hc]
  have h2 : Complex.exp (Complex.I * (n : ℂ) * (π : ℂ)) =
      Complex.exp (Complex.I * (n : ℂ) * ((-π : ℝ) : ℂ)) :=
    Complex.exp_eq_exp_iff_exists_int.mpr ⟨n, by push_cast; ring⟩
  rw [h2, sub_self, zero_div]
theorem integral_charCM_of_ne (u : orthLattice μ) (hu : u ≠ 0) :
    ∫ η, charCM u η ∂torusMeasure μ = 0 := by
  obtain ⟨l, hl⟩ : ∃ l : TransverseAxis μ, (u : Fin 4 → ℤ) l.1 ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hu (Subtype.ext (funext fun i => ?_))
    by_cases hi : i = μ
    · subst hi
      exact u.2
    · exact hc ⟨i, hi⟩
  have hbox : fundamentalBox μ = Set.pi univ fun _ => Ioc (-π) π := by
    ext η
    simp [fundamentalBox, Set.mem_pi]
  have hpt : ∀ x : TransverseAxis μ → ℝ, charCM u (torusProj μ x) =
      ∏ l, Complex.exp (Complex.I * ((x l * ((u : Fin 4 → ℤ) l.1 : ℤ) : ℝ) : ℂ)) := by
    intro x
    rw [charCM_apply, torusCharacter_eq_prod_fourier]
    exact Finset.prod_congr rfl fun l _ => fourier_coe_eq_exp (x l) _
  rw [torusMeasure, integral_map (continuous_torusProj μ).aemeasurable
    (charCM u).continuous.aestronglyMeasurable, hbox, volume_pi, Measure.restrict_pi_pi]
  simp_rw [hpt]
  rw [integral_fintype_prod_eq_prod
    (f := fun (l : TransverseAxis μ) (t : ℝ) => Complex.exp (Complex.I * ((t * ((u : Fin 4 → ℤ) l.1 : ℤ) : ℝ) : ℂ)))]
  exact Finset.prod_eq_zero (Finset.mem_univ l) (integral_exp_int_mul_Ioc hl)
theorem integral_charCM_mul_torusFourierSeries (M : Measure (DualTorus μ)) [IsFiniteMeasure M]
    (hs : Summable fun w => ‖torusFourierCoeff μ M w‖) (w : orthLattice μ) :
    ∫ η, charCM w η * torusFourierSeries μ M η ∂torusMeasure μ =
      torusFourierCoeff μ M w := by
  let G : orthLattice μ → DualTorus μ → ℂ :=
    fun v η => torusFourierCoeff μ M v * charCM (w - v) η
  have hGi : ∀ v, Integrable (G v) (torusMeasure μ) := fun v =>
    (integrable_of_continuousMap _ (charCM (w - v))).const_mul _
  have hGn : ∀ v η, ‖G v η‖ = ‖torusFourierCoeff μ M v‖ := by
    intro v η
    simp [G, charCM_apply, norm_torusCharacter]
  have hS : Summable fun v => ∫ η, ‖G v η‖ ∂torusMeasure μ := by
    simp_rw [hGn, integral_const]
    exact hs.const_smul _
  have hH := hasSum_integral_of_summable_integral_norm hGi hS
  have hval : ∀ v, ∫ η, G v η ∂torusMeasure μ =
      if v = w then torusFourierCoeff μ M w * (((2 * π) ^ 3 : ℝ) : ℂ) else 0 := by
    intro v
    rw [integral_const_mul]
    split_ifs with hv
    · subst hv
      rw [sub_self, charCM_zero]
      simp [torusMeasure_real_univ]
    · rw [integral_charCM_of_ne _ (sub_ne_zero.mpr (Ne.symm hv)), mul_zero]
  have hH2 : HasSum (fun v => ∫ η, G v η ∂torusMeasure μ)
      (torusFourierCoeff μ M w * (((2 * π) ^ 3 : ℝ) : ℂ)) := by
    simp_rw [hval]
    exact hasSum_ite_eq w _
  have e := hH.unique hH2
  have hpt : ∀ η, charCM w η * torusFourierSeries μ M η =
      (((2 * π) ^ 3)⁻¹ : ℝ) * ∑' v, G v η := by
    intro η
    rw [torusFourierSeries, mul_left_comm]
    congr 1
    rw [← tsum_mul_left]
    refine tsum_congr fun v => ?_
    rw [torusFourierTerm_eq_mul_charCM, mul_left_comm]
    simp only [G, sub_eq_add_neg, charCM_add, ContinuousMap.mul_apply]
  simp_rw [hpt]
  rw [integral_const_mul, e]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
theorem summableFourierCoeffTheorem_proof : SummableFourierCoeffTheorem := by
  intro μ M _ hs
  have hb : ∀ w η, ‖torusFourierTerm μ M w η‖ = ‖torusFourierCoeff μ M w‖ := by
    intro w η
    rw [torusFourierTerm_eq_mul_charCM, norm_mul, charCM_apply, norm_torusCharacter, mul_one]
  have hsum : ∀ η, Summable fun w => ‖torusFourierTerm μ M w η‖ := fun η => by
    simpa only [hb] using hs
  have hc : (0 : ℝ) ≤ ((2 * π) ^ 3)⁻¹ := by positivity
  have hU : TendstoUniformly
      (fun (s : Finset (orthLattice μ)) (η : DualTorus μ) =>
        (((2 * π) ^ 3)⁻¹ : ℝ) * ∑ w ∈ s, torusFourierTerm μ M w η)
      (torusFourierSeries μ M) atTop :=
    ((ContinuousLinearMap.mul ℂ ℂ) ((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ)).uniformContinuous.comp_tendstoUniformly
      (tendstoUniformly_tsum hs fun w η => (hb w η).le)
  have hterm : ∀ w, Continuous (torusFourierTerm μ M w) := fun w => by
    rw [show torusFourierTerm μ M w = fun η => torusFourierCoeff μ M w * charCM (-w) η
      from funext (torusFourierTerm_eq_mul_charCM M w)]
    exact continuous_const.mul (charCM (-w)).continuous
  have hcont : Continuous (torusFourierSeries μ M) :=
    hU.continuous (Frequently.of_forall fun s =>
      continuous_const.mul (continuous_finsetSum _ fun w _ => hterm w))
  let h : C(DualTorus μ, ℂ) := ⟨torusFourierSeries μ M, hcont⟩
  have K : ∀ f : C(DualTorus μ, ℂ), ∫ x, f x ∂M = ∫ x, f x * h x ∂torusMeasure μ := by
    have hD : integralCLM M = (integralCLM (torusMeasure μ)).comp
        ((ContinuousLinearMap.mul ℂ C(DualTorus μ, ℂ)).flip h) := by
      refine ContinuousLinearMap.ext_on dense_span_charCM ?_
      rintro - ⟨w, rfl⟩
      exact (integral_charCM_mul_torusFourierSeries M hs w).symm
    exact fun f => DFunLike.congr_fun hD f
  obtain ⟨hpos, hM⟩ := eq_withDensity_of_integral_eq M (torusMeasure μ) h K
  refine ⟨hsum, hU, hcont, hM, fun η => ⟨(hpos η).1, (hpos η).2, ?_⟩⟩
  have hn : ‖torusFourierSeries μ M η‖ ≤
      ((2 * π) ^ 3)⁻¹ * ∑' w, ‖torusFourierCoeff μ M w‖ := by
    rw [torusFourierSeries, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
    refine mul_le_mul_of_nonneg_left ?_ hc
    have := norm_tsum_le_tsum_norm (hsum η)
    simpa only [hb] using this
  exact (Complex.re_le_norm _).trans hn
end YangMills.Construction.ReflectionPositivity.EnergyMomentum.FourierDensity
