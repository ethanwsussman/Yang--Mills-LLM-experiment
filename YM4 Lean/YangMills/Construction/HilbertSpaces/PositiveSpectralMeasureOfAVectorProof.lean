import YangMills.Construction.SpectralCalculus.VectorSpectralMeasure
import YangMills.Construction.TwoPoints.SmearedGroupAndTheTwoBounds
import YangMills.Construction.TwoPoints.TransformsConvolutionPowersAndDensity
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported
noncomputable section
namespace YangMills.Construction.TwoPoints.LineTransforms.VectorMeasure
theorem cocompact_unitStrip_eq :
    cocompact UnitStrip = comap Prod.snd (comap (fun q : ℝ => |q|) atTop) := by
  rw [← Filter.coprod_cocompact, cocompact_eq_bot, bot_coprod]
  congr 1
  rw [cocompact_eq_atBot_atTop]
  exact comap_abs_atTop.symm
theorem tendsto_cocompact_of_mem_stripC0 {F : UnitStrip → ℂ} (hF : F ∈ stripC0) :
    Tendsto F (cocompact UnitStrip) (𝓝 0) := by
  rw [cocompact_unitStrip_eq, tendsto_zero_iff_enorm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hF.2.comp tendsto_comap) (fun _ => zero_le) fun y => ?_
  exact le_iSup (fun a : unitInterval => ‖F (a, y.2)‖ₑ) y.1
theorem mem_stripC0_of_tendsto {F : UnitStrip → ℂ} (hc : Continuous F)
    (h : Tendsto F (cocompact UnitStrip) (𝓝 0)) : F ∈ stripC0 := by
  refine ⟨hc, ?_⟩
  have h' := tendsto_zero_iff_enorm_tendsto_zero.1 h
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have h2 := ENNReal.tendsto_nhds_zero.1 h' ε hε
  rw [cocompact_unitStrip_eq, eventually_comap] at h2
  filter_upwards [h2] with q hq
  exact iSup_le fun a => hq (a, q) rfl
def toZeroAtInfty (F : UnitStrip → ℂ) (hF : F ∈ stripC0) : C₀(UnitStrip, ℂ) :=
  ⟨⟨F, hF.1⟩, tendsto_cocompact_of_mem_stripC0 hF⟩
theorem zeroAtInfty_mem_stripC0 (F : C₀(UnitStrip, ℂ)) : (F : UnitStrip → ℂ) ∈ stripC0 :=
  mem_stripC0_of_tendsto (map_continuous F) F.zero_at_infty'
theorem uniformNorm_eq_norm (F : C₀(UnitStrip, ℂ)) :
    TestFunctions.uniformNorm (F : UnitStrip → ℂ) = ‖F‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, BoundedContinuousFunction.norm_eq_iSup_norm]
  rfl
theorem norm_apply_le_norm (F : C₀(UnitStrip, ℂ)) (y : UnitStrip) : ‖F y‖ ≤ ‖F‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact F.toBCF.norm_coe_le_norm y
theorem norm_le_of_forall (F : C₀(UnitStrip, ℂ)) {c : ℝ} (hc : 0 ≤ c) (h : ∀ y, ‖F y‖ ≤ c) :
    ‖F‖ ≤ c := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le hc).2 h
def postcomp (φ : ℂ → ℂ) (hφ : Continuous φ) (h0 : φ 0 = 0) (F : C₀(UnitStrip, ℂ)) :
    C₀(UnitStrip, ℂ) :=
  ⟨⟨φ ∘ F, hφ.comp (map_continuous F)⟩, (hφ.tendsto' 0 0 h0).comp F.zero_at_infty'⟩
def cutoff (j : ℕ) (y : UnitStrip) : ℝ := max 0 (min 1 ((j : ℝ) + 1 - |y.2|))
theorem continuous_cutoff (j : ℕ) : Continuous (cutoff j) := by
  unfold cutoff
  fun_prop
theorem cutoff_nonneg (j : ℕ) (y : UnitStrip) : 0 ≤ cutoff j y := le_max_left _ _
theorem cutoff_le_one (j : ℕ) (y : UnitStrip) : cutoff j y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)
theorem cutoff_eq_one {j : ℕ} {y : UnitStrip} (h : |y.2| ≤ j) : cutoff j y = 1 := by
  have : (1 : ℝ) ≤ (j : ℝ) + 1 - |y.2| := by linarith
  simp [cutoff, this]
theorem cutoff_eq_zero {j : ℕ} {y : UnitStrip} (h : (j : ℝ) + 1 ≤ |y.2|) : cutoff j y = 0 := by
  have h1 : (j : ℝ) + 1 - |y.2| ≤ 0 := by linarith
  have h2 : min 1 ((j : ℝ) + 1 - |y.2|) ≤ 0 := (min_le_right _ _).trans h1
  simp [cutoff, h2]
def truncate (f : UnitStrip → ℝ) (hf : Continuous f) (j : ℕ) : C_c(UnitStrip, ℝ) :=
  ⟨⟨fun y => f y * cutoff j y, hf.mul (continuous_cutoff j)⟩, by
    refine HasCompactSupport.intro (K := univ ×ˢ Icc (-((j : ℝ) + 1)) ((j : ℝ) + 1))
      (isCompact_univ.prod isCompact_Icc) fun y hy => ?_
    have h : (j : ℝ) + 1 ≤ |y.2| := by
      by_contra hlt
      replace hlt := not_le.1 hlt
      exact hy ⟨mem_univ _, (abs_lt.1 hlt).1.le, (abs_lt.1 hlt).2.le⟩
    simp [cutoff_eq_zero h]⟩
theorem truncate_apply (f : UnitStrip → ℝ) (hf : Continuous f) (j : ℕ) (y : UnitStrip) :
    truncate f hf j y = f y * cutoff j y := rfl
def realToC0 (f : C_c(UnitStrip, ℝ)) : C₀(UnitStrip, ℂ) :=
  ⟨⟨fun y => (f y : ℂ), Complex.continuous_ofReal.comp (map_continuous f)⟩,
    (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).comp
      (ZeroAtInftyContinuousMapClass.zero_at_infty f)⟩
theorem realToC0_apply (f : C_c(UnitStrip, ℝ)) (y : UnitStrip) : realToC0 f y = (f y : ℂ) := rfl
theorem tendsto_realToC0_truncate (F : C₀(UnitStrip, ℂ)) (hF : ∀ y, (F y).im = 0)
    (hf : Continuous fun y => (F y).re) :
    Tendsto (fun j => realToC0 (truncate (fun y => (F y).re) hf j)) atTop (𝓝 F) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 := (Metric.tendsto_nhds.1 F.zero_at_infty') (ε / 2) (half_pos hε)
  rw [cocompact_unitStrip_eq, eventually_comap, eventually_comap, eventually_atTop] at h1
  obtain ⟨R, hR⟩ := h1
  refine ⟨⌈R⌉₊, fun j hj => ?_⟩
  have hjR : R ≤ j := (Nat.le_ceil R).trans (by exact_mod_cast hj)
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (norm_le_of_forall _ (half_pos hε).le fun y => ?_) (half_lt_self hε)
  have hFy : F y = ((F y).re : ℂ) := by
    apply Complex.ext <;> simp [hF y]
  change ‖realToC0 (truncate (fun y => (F y).re) hf j) y - F y‖ ≤ ε / 2
  rw [realToC0_apply, truncate_apply]
  by_cases hq : |y.2| ≤ j
  · rw [cutoff_eq_one hq]
    simp only [mul_one]
    rw [← hFy]
    simpa using (half_pos hε).le
  · replace hq := not_le.1 hq
    have h2 : dist ((F : UnitStrip → ℂ) y) 0 < ε / 2 :=
      hR |y.2| (hjR.trans hq.le) y.2 rfl y rfl
    rw [dist_zero_right] at h2
    have h3 : (((F y).re * cutoff j y : ℝ) : ℂ) - F y = -(((1 - cutoff j y : ℝ) : ℂ) * F y) := by
      conv_lhs => rw [hFy]
      conv_rhs => rw [hFy]
      push_cast
      simp only [Complex.ofReal_re]
      ring
    rw [h3, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [cutoff_le_one j y])]
    have h4 : 1 - cutoff j y ≤ 1 := by linarith [cutoff_nonneg j y]
    nlinarith [norm_nonneg (F y), cutoff_nonneg j y, cutoff_le_one j y]
section Functional
variable (Λ : C₀(UnitStrip, ℂ) →L[ℂ] ℂ)
theorem im_apply_eq_zero_of_real
    (hpos : ∀ F : C₀(UnitStrip, ℂ), (∀ y, (F y).im = 0 ∧ 0 ≤ (F y).re) →
      (Λ F).im = 0 ∧ 0 ≤ (Λ F).re)
    (F : C₀(UnitStrip, ℂ)) (hF : ∀ y, (F y).im = 0) : (Λ F).im = 0 := by
  let P := postcomp (fun z => ((max z.re 0 : ℝ) : ℂ)) (by fun_prop) (by simp) F
  let N := postcomp (fun z => ((max (-z.re) 0 : ℝ) : ℂ)) (by fun_prop) (by simp) F
  have hFPN : F = P - N := by
    ext y
    change F y = ((max (F y).re 0 : ℝ) : ℂ) - ((max (-(F y).re) 0 : ℝ) : ℂ)
    rw [← Complex.ofReal_sub, max_zero_sub_max_neg_zero_eq_self]
    apply Complex.ext <;> simp [hF y]
  have hP := hpos P fun y => by
    change (((max (F y).re 0 : ℝ) : ℂ)).im = 0 ∧ 0 ≤ (((max (F y).re 0 : ℝ) : ℂ)).re
    simp
  have hN := hpos N fun y => by
    change (((max (-(F y).re) 0 : ℝ) : ℂ)).im = 0 ∧ 0 ≤ (((max (-(F y).re) 0 : ℝ) : ℂ)).re
    simp
  rw [hFPN, map_sub, Complex.sub_im, hP.1, hN.1, sub_zero]
def toRealPositive
    (hpos : ∀ F : C₀(UnitStrip, ℂ), (∀ y, (F y).im = 0 ∧ 0 ≤ (F y).re) →
      (Λ F).im = 0 ∧ 0 ≤ (Λ F).re) : C_c(UnitStrip, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => (Λ (realToC0 f)).re
      map_add' := fun f g => by
        have : realToC0 (f + g) = realToC0 f + realToC0 g := by
          ext y
          simp [realToC0_apply]
        rw [this, map_add, Complex.add_re]
      map_smul' := fun c f => by
        have : realToC0 (c • f) = (c : ℂ) • realToC0 f := by
          ext y
          simp [realToC0_apply]
        rw [this, map_smul, smul_eq_mul, Complex.re_ofReal_mul]
        rfl }
    fun f hf => (hpos (realToC0 f) fun y => by
      have : 0 ≤ f y := hf y
      simp [realToC0_apply, this]).2
theorem toRealPositive_apply
    (hpos : ∀ F : C₀(UnitStrip, ℂ), (∀ y, (F y).im = 0 ∧ 0 ≤ (F y).re) →
      (Λ F).im = 0 ∧ 0 ≤ (Λ F).re) (f : C_c(UnitStrip, ℝ)) :
    toRealPositive Λ hpos f = (Λ (realToC0 f)).re := rfl
theorem exists_finiteMeasure_rep (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ F, ‖Λ F‖ ≤ C * ‖F‖)
    (hpos : ∀ F : C₀(UnitStrip, ℂ), (∀ y, (F y).im = 0 ∧ 0 ≤ (F y).re) →
      (Λ F).im = 0 ∧ 0 ≤ (Λ F).re) :
    ∃ ν : Measure UnitStrip, IsFiniteMeasure ν ∧ ∀ F : C₀(UnitStrip, ℂ), Λ F = ∫ y, F y ∂ν := by
  set Λr := toRealPositive Λ hpos with hΛr
  set ν := RealRMK.rieszMeasure Λr with hν
  have hrep : ∀ f : C_c(UnitStrip, ℝ), ∫ y, f y ∂ν = (Λ (realToC0 f)).re := fun f =>
    RealRMK.integral_rieszMeasure Λr f
  have hK : ∀ j : ℕ, ν (univ ×ˢ Icc (-(j : ℝ)) (j : ℝ)) ≤ ENNReal.ofReal C := by
    intro j
    have hc : Continuous fun _ : UnitStrip => (1 : ℝ) := continuous_const
    have h1 := RealRMK.rieszMeasure_le_of_eq_one Λr (f := truncate (fun _ => 1) hc j)
      (fun y => by simpa [truncate_apply] using cutoff_nonneg j y)
      (K := univ ×ˢ Icc (-(j : ℝ)) (j : ℝ)) (isCompact_univ.prod isCompact_Icc)
      (fun y hy => by
        have : |y.2| ≤ j := abs_le.2 hy.2
        simp [truncate_apply, cutoff_eq_one this])
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [toRealPositive_apply]
    have h2 : ‖realToC0 (truncate (fun _ => 1) hc j)‖ ≤ 1 :=
      norm_le_of_forall _ zero_le_one fun y => by
        rw [realToC0_apply, truncate_apply, Complex.norm_real, one_mul, Real.norm_eq_abs,
          abs_of_nonneg (cutoff_nonneg j y)]
        exact cutoff_le_one j y
    calc (Λ (realToC0 (truncate (fun _ => 1) hc j))).re
          ≤ ‖Λ (realToC0 (truncate (fun _ => 1) hc j))‖ := Complex.re_le_norm _
      _ ≤ C * ‖realToC0 (truncate (fun _ => 1) hc j)‖ := hC _
      _ ≤ C * 1 := by gcongr
      _ = C := mul_one C
  have hU : (univ : Set UnitStrip) = ⋃ j : ℕ, univ ×ˢ Icc (-(j : ℝ)) (j : ℝ) := by
    symm
    rw [eq_univ_iff_forall]
    intro y
    obtain ⟨j, hj⟩ := exists_nat_ge |y.2|
    exact mem_iUnion.2 ⟨j, mem_univ _, abs_le.1 hj⟩
  have hmono : Monotone fun j : ℕ => (univ ×ˢ Icc (-(j : ℝ)) (j : ℝ) : Set UnitStrip) := by
    intro i j hij y hy
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    exact ⟨mem_univ _, by linarith [hy.2.1], by linarith [hy.2.2]⟩
  have hfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hU, hmono.measure_iUnion]
    exact lt_of_le_of_lt (iSup_le hK) ENNReal.ofReal_lt_top
  have hint : ∀ F : C₀(UnitStrip, ℂ), Integrable (F : UnitStrip → ℂ) ν := fun F =>
    BoundedContinuousFunction.integrable ν F.toBCF
  have hreal : ∀ F : C₀(UnitStrip, ℂ), (∀ y, (F y).im = 0) → Λ F = ∫ y, F y ∂ν := by
    intro F hF
    have hf : Continuous fun y => (F y).re := Complex.continuous_re.comp (map_continuous F)
    have hconv := tendsto_realToC0_truncate F hF hf
    have hΛ := (Λ.continuous.tendsto F).comp hconv
    have hvals : ∀ j, Λ (realToC0 (truncate (fun y => (F y).re) hf j)) =
        ((∫ y, truncate (fun y => (F y).re) hf j y ∂ν : ℝ) : ℂ) := by
      intro j
      rw [hrep]
      apply Complex.ext
      · simp
      · simpa using im_apply_eq_zero_of_real Λ hpos _ fun y => by simp [realToC0_apply]
    have hlim : Tendsto (fun j => ∫ y, truncate (fun y => (F y).re) hf j y ∂ν) atTop
        (𝓝 (∫ y, (F y).re ∂ν)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
        (fun j => (map_continuous _).aestronglyMeasurable) (integrable_const _)
        (fun j => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
      · rw [truncate_apply, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (cutoff_nonneg j y)]
        calc |(F y).re| * cutoff j y ≤ |(F y).re| * 1 := by
              gcongr
              exact cutoff_le_one j y
          _ ≤ ‖F y‖ := by simpa using Complex.abs_re_le_norm (F y)
          _ ≤ ‖F‖ := norm_apply_le_norm F y
      · refine tendsto_const_nhds.congr' ?_
        obtain ⟨N, hN⟩ := exists_nat_ge |y.2|
        filter_upwards [eventually_ge_atTop N] with j hj
        have : |y.2| ≤ j := hN.trans (by exact_mod_cast hj)
        simp [truncate_apply, cutoff_eq_one this]
    have h2 : Tendsto (fun j => Λ (realToC0 (truncate (fun y => (F y).re) hf j))) atTop
        (𝓝 ((∫ y, (F y).re ∂ν : ℝ) : ℂ)) := by
      simp only [hvals]
      exact (Complex.continuous_ofReal.tendsto _).comp hlim
    have h3 : Λ F = ((∫ y, (F y).re ∂ν : ℝ) : ℂ) := tendsto_nhds_unique hΛ h2
    rw [h3, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    apply Complex.ext <;> simp [hF y]
  refine ⟨ν, hfin, fun F => ?_⟩
  let R := postcomp (fun z => (z.re : ℂ)) (by fun_prop) (by simp) F
  let I := postcomp (fun z => (z.im : ℂ)) (by fun_prop) (by simp) F
  have hFRI : F = R + Complex.I • I := by
    ext y
    change F y = ((F y).re : ℂ) + Complex.I * ((F y).im : ℂ)
    rw [mul_comm]
    exact (Complex.re_add_im (F y)).symm
  have hR := hreal R fun y => by change (((F y).re : ℂ)).im = 0; simp
  have hI := hreal I fun y => by change (((F y).im : ℂ)).im = 0; simp
  have hsum : ∫ y, F y ∂ν = ∫ y, R y ∂ν + Complex.I * ∫ y, I y ∂ν := by
    rw [← integral_const_mul, ← integral_add (hint R) ((hint I).const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    change F y = ((F y).re : ℂ) + Complex.I * ((F y).im : ℂ)
    rw [mul_comm]
    exact (Complex.re_add_im (F y)).symm
  rw [hsum, ← hR, ← hI]
  conv_lhs => rw [hFRI]
  rw [map_add, map_smul, smul_eq_mul]
end Functional
theorem exists_bounded_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (G : Submodule ℂ (E × ℂ)) (C : ℝ) (hC0 : 0 ≤ C) (hG : ∀ x ∈ G, ‖x.2‖ ≤ C * ‖x.1‖) :
    ∃ Λ : E →L[ℂ] ℂ, (∀ x ∈ G, Λ x.1 = x.2) ∧ ∀ F, ‖Λ F‖ ≤ C * ‖F‖ := by
  have hg : ∀ x ∈ G, x.1 = 0 → x.2 = 0 := fun x hx h0 => by
    have := hG x hx
    rw [h0, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let f : G.toLinearPMap.domain →ₗ[ℂ] ℂ := G.toLinearPMap.toFun
  have hmem : ∀ x : G.toLinearPMap.domain, ((x : E), G.toLinearPMap x) ∈ G := fun x =>
    Submodule.mem_graph_toLinearPMap hg x
  let fc : StrongDual ℂ G.toLinearPMap.domain := f.mkContinuous C fun x => hG _ (hmem x)
  obtain ⟨Λ, hΛ, hn⟩ := exists_extension_norm_eq G.toLinearPMap.domain fc
  refine ⟨Λ, fun x hx => ?_, fun F => ?_⟩
  · have hd : x.1 ∈ G.toLinearPMap.domain := by
      rw [Submodule.toLinearPMap_domain]
      exact ⟨x, hx, rfl⟩
    have h1 := hΛ ⟨x.1, hd⟩
    have h2 : (x.1, G.toLinearPMap ⟨x.1, hd⟩) ∈ G := hmem ⟨x.1, hd⟩
    have h3 : (0, x.2 - G.toLinearPMap ⟨x.1, hd⟩) ∈ G := by
      have h5 := G.sub_mem hx h2
      have h6 : x - (x.1, G.toLinearPMap ⟨x.1, hd⟩) = (0, x.2 - G.toLinearPMap ⟨x.1, hd⟩) :=
        Prod.ext (sub_self _) rfl
      rwa [h6] at h5
    have h4 := hg _ h3 rfl
    change Λ x.1 = fc ⟨x.1, hd⟩ at h1
    rw [h1]
    change G.toLinearPMap ⟨x.1, hd⟩ = x.2
    exact (sub_eq_zero.1 h4).symm
  · calc ‖Λ F‖ ≤ ‖Λ‖ * ‖F‖ := Λ.le_opNorm F
      _ ≤ C * ‖F‖ := by
        gcongr
        rw [hn]
        exact LinearMap.mkContinuous_norm_le _ hC0 _
theorem integrable_mul_cexp {g : ℝ → ℂ} (hg : g ∈ c1Functions) (q : ℝ) :
    Integrable fun s : ℝ => g s * Complex.exp (Complex.I * (s : ℂ) * (q : ℂ)) := by
  have hc : Continuous g := hg.1.continuous
  have hk : HasCompactSupport g := hg.2.1
  exact (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hk.mul_right
theorem lineTransform_add {g h : ℝ → ℂ} (hg : g ∈ c1Functions) (hh : h ∈ c1Functions) (q : ℝ) :
    lineTransform (g + h) q = lineTransform g q + lineTransform h q := by
  simp only [lineTransform, lebesgueIntegral, integralWrt, Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_cexp hg q) (integrable_mul_cexp hh q)
theorem lineTransform_smul (c : ℂ) (g : ℝ → ℂ) (q : ℝ) :
    lineTransform (c • g) q = c * lineTransform g q := by
  simp only [lineTransform, lebesgueIntegral, integralWrt, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _
section Pairs
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : ℝ≥0 → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H)
def weightedPair (τ : ℝ≥0) (j : ℕ) (g : ℝ → ℂ) : (UnitStrip → ℂ) × (H →L[ℂ] H) :=
  (fun p => (intervalRpow ((j : ℝ≥0) * τ) p.1 : ℂ) * lineTransform g p.2,
    T ((j : ℝ≥0) * τ) * smear U g)
theorem sum_weightedPair (τ : ℝ≥0) (J : ℕ) (g : ℕ → ℝ → ℂ) :
    (transformSum τ J g, smearedSum T U τ J g) =
      ∑ j ∈ Finset.range (J + 1), weightedPair T U τ j (g j) := by
  apply Prod.ext
  · rw [Prod.fst_sum]
    funext p
    simp [transformSum, weightedPair, Finset.sum_apply]
  · rw [Prod.snd_sum]
    simp [smearedSum, weightedPair]
def dyadicStep (i : ℕ) : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ i
theorem dyadicStep_pos (i : ℕ) : 0 < dyadicStep i := by
  unfold dyadicStep
  positivity
theorem mul_dyadicStep_mem (j i : ℕ) : (j : ℝ≥0) * dyadicStep i ∈ dyadics :=
  ⟨i, j, by simp [dyadicStep, zpow_neg]⟩
def stepPairs (i : ℕ) : Submodule ℂ ((UnitStrip → ℂ) × (H →L[ℂ] H)) :=
  Submodule.span ℂ {x | ∃ j : ℕ, ∃ g ∈ c1Functions, x = weightedPair T U (dyadicStep i) j g}
def transformPairs : Submodule ℂ ((UnitStrip → ℂ) × (H →L[ℂ] H)) :=
  Submodule.span ℂ {x | ∃ t ∈ dyadics, ∃ g ∈ c1Functions,
    x = (fun p : UnitStrip => (intervalRpow t p.1 : ℂ) * lineTransform g p.2, T t * smear U g)}
theorem stepPairs_le_succ (i : ℕ) : stepPairs T U i ≤ stepPairs T U (i + 1) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, g, hg, rfl⟩
  refine Submodule.subset_span ⟨2 * j, g, hg, ?_⟩
  have h : ((2 * j : ℕ) : ℝ≥0) * dyadicStep (i + 1) = (j : ℝ≥0) * dyadicStep i := by
    simp only [dyadicStep, pow_succ]
    push_cast
    field_simp
  simp only [weightedPair, h]
theorem stepPairs_mono : Monotone (stepPairs T U) :=
  monotone_nat_of_le_succ (stepPairs_le_succ T U)
theorem stepPairs_le_transformPairs (i : ℕ) : stepPairs T U i ≤ transformPairs T U := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, g, hg, rfl⟩
  exact Submodule.subset_span ⟨_, mul_dyadicStep_mem j i, g, hg, rfl⟩
theorem exists_stepPairs {x : (UnitStrip → ℂ) × (H →L[ℂ] H)} (hx : x ∈ transformPairs T U) :
    ∃ i, x ∈ stepPairs T U i := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨t, ⟨i, j, ht⟩, g, hg, rfl⟩ := h
    refine ⟨i, Submodule.subset_span ⟨j, g, hg, ?_⟩⟩
    have h : t = (j : ℝ≥0) * dyadicStep i := NNReal.eq (by simpa [dyadicStep, zpow_neg] using ht)
    rw [h]
    rfl
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨k, hk⟩ := hy
    exact ⟨max i k, Submodule.add_mem _ (stepPairs_mono T U (le_max_left _ _) hi)
      (stepPairs_mono T U (le_max_right _ _) hk)⟩
  | smul c x _ hx =>
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, Submodule.smul_mem _ c hi⟩
variable {T U}
theorem smear_zero (hL : SmearingCalculus U) : smear U 0 = 0 := by
  have h := hL.linear 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
  simpa using h
theorem smear_add (hL : SmearingCalculus U) {g h : ℝ → ℂ}
    (hg : g ∈ c1Functions) (hh : h ∈ c1Functions) :
    smear U (g + h) = smear U g + smear U h := by
  simpa using hL.linear g hg h hh 1
theorem smear_smul (hL : SmearingCalculus U) (c : ℂ) {g : ℝ → ℂ} (hg : g ∈ c1Functions) :
    smear U (c • g) = c • smear U g := by
  have h := hL.linear 0 (Submodule.zero_mem _) g hg c
  simpa [smear_zero hL] using h
theorem weightedPair_zero (hL : SmearingCalculus U) (τ : ℝ≥0) (j : ℕ) :
    weightedPair T U τ j 0 = 0 := by
  apply Prod.ext
  · funext p
    have h : lineTransform 0 p.2 = 0 := by
      simpa using lineTransform_smul 0 0 p.2
    simp [weightedPair, h]
  · simp [weightedPair, smear_zero hL]
theorem weightedPair_add (hL : SmearingCalculus U) (τ : ℝ≥0) (j : ℕ) {g h : ℝ → ℂ}
    (hg : g ∈ c1Functions) (hh : h ∈ c1Functions) :
    weightedPair T U τ j (g + h) = weightedPair T U τ j g + weightedPair T U τ j h := by
  apply Prod.ext
  · funext p
    simp [weightedPair, lineTransform_add hg hh, mul_add]
  · simp [weightedPair, smear_add hL hg hh, mul_add]
theorem weightedPair_smul (hL : SmearingCalculus U) (τ : ℝ≥0) (j : ℕ) (c : ℂ) {g : ℝ → ℂ}
    (hg : g ∈ c1Functions) :
    weightedPair T U τ j (c • g) = c • weightedPair T U τ j g := by
  apply Prod.ext
  · funext p
    simp only [weightedPair, lineTransform_smul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    ring
  · simp [weightedPair, smear_smul hL c hg]
theorem sum_weightedPair_extend (hL : SmearingCalculus U) (τ : ℝ≥0) {J J' : ℕ} (hJ : J ≤ J')
    {g : ℕ → ℝ → ℂ} (hg : ∀ j, J < j → g j = 0) :
    ∑ j ∈ Finset.range (J' + 1), weightedPair T U τ j (g j) =
      ∑ j ∈ Finset.range (J + 1), weightedPair T U τ j (g j) := by
  symm
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
  have : J < j := by
    simp only [Finset.mem_range] at hj
    omega
  rw [hg j this, weightedPair_zero hL]
theorem exists_sum_rep (hL : SmearingCalculus U) {i : ℕ} {x : (UnitStrip → ℂ) × (H →L[ℂ] H)}
    (hx : x ∈ stepPairs T U i) :
    ∃ (J : ℕ) (g : ℕ → ℝ → ℂ), (∀ j, g j ∈ c1Functions) ∧ (∀ j, J < j → g j = 0) ∧
      x = ∑ j ∈ Finset.range (J + 1), weightedPair T U (dyadicStep i) j (g j) := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨j, g, hg, rfl⟩ := h
    refine ⟨j, fun k => if k = j then g else 0, fun k => ?_, fun k hk => ?_, ?_⟩
    · by_cases h : k = j
      · simpa [h] using hg
      · simp [h]
    · simp [hk.ne']
    · rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        simp [hk, weightedPair_zero hL]
      · simp
  | zero =>
    refine ⟨0, fun _ => 0, fun _ => Submodule.zero_mem _, fun _ _ => rfl, ?_⟩
    simp [weightedPair_zero hL]
  | add x y _ _ hx hy =>
    obtain ⟨J, g, hg, hg0, rfl⟩ := hx
    obtain ⟨J', g', hg', hg0', rfl⟩ := hy
    refine ⟨max J J', fun j => g j + g' j, fun j => Submodule.add_mem _ (hg j) (hg' j),
      fun j hj => ?_, ?_⟩
    · change g j + g' j = 0
      rw [hg0 j (lt_of_le_of_lt (le_max_left _ _) hj),
        hg0' j (lt_of_le_of_lt (le_max_right _ _) hj), add_zero]
    · rw [← sum_weightedPair_extend hL _ (le_max_left J J') hg0,
        ← sum_weightedPair_extend hL _ (le_max_right J J') hg0', ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => (weightedPair_add hL _ _ (hg j) (hg' j)).symm
  | smul c x _ hx =>
    obtain ⟨J, g, hg, hg0, rfl⟩ := hx
    refine ⟨J, fun j => c • g j, fun j => Submodule.smul_mem _ c (hg j), fun j hj => ?_, ?_⟩
    · change c • g j = 0
      rw [hg0 j hj, smul_zero]
    · rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => (weightedPair_smul hL _ _ c (hg j)).symm
theorem exists_sum_rep_of_mem (hL : SmearingCalculus U) {x : (UnitStrip → ℂ) × (H →L[ℂ] H)}
    (hx : x ∈ transformPairs T U) :
    ∃ (i J : ℕ) (g : ℕ → ℝ → ℂ), (∀ j, g j ∈ c1Functions) ∧
      x = (transformSum (dyadicStep i) J g, smearedSum T U (dyadicStep i) J g) := by
  obtain ⟨i, hi⟩ := exists_stepPairs T U hx
  obtain ⟨J, g, hg, -, h⟩ := exists_sum_rep hL hi
  exact ⟨i, J, g, hg, by rw [sum_weightedPair]; exact h⟩
theorem norm_inner_snd_le (hL : SmearingCalculus U)
    (hb : ∀ (τ : ℝ≥0) (J : ℕ) (g : ℕ → ℝ → ℂ), 0 < τ → (∀ j ≤ J, g j ∈ c1Functions) →
      SmearedSumBounds T U τ J g)
    {x : (UnitStrip → ℂ) × (H →L[ℂ] H)} (hx : x ∈ transformPairs T U) (w : H) :
    ‖inner ℂ w (x.2 w)‖ ≤ TestFunctions.uniformNorm x.1 * ‖w‖ ^ 2 := by
  obtain ⟨i, J, g, hg, rfl⟩ := exists_sum_rep_of_mem hL hx
  exact (hb _ J g (dyadicStep_pos i) fun j _ => hg j).norm_inner_le w
theorem exists_normSq_pair (hL : SmearingCalculus U)
    (hb : ∀ (τ : ℝ≥0) (J : ℕ) (g : ℕ → ℝ → ℂ), 0 < τ → (∀ j ≤ J, g j ∈ c1Functions) →
      SmearedSumBounds T U τ J g)
    {x : (UnitStrip → ℂ) × (H →L[ℂ] H)} (hx : x ∈ transformPairs T U) :
    ∃ Φ : H →L[ℂ] H, (fun p => ((‖x.1 p‖ ^ 2 : ℝ) : ℂ), Φ) ∈ transformPairs T U ∧
      ∀ w, ((‖x.2 w‖ ^ 2 : ℝ) : ℂ) = inner ℂ w (Φ w) := by
  obtain ⟨i, J, g, hg, rfl⟩ := exists_sum_rep_of_mem hL hx
  have hB := hb _ J g (dyadicStep_pos i) fun j _ => hg j
  refine ⟨smearedSum T U (dyadicStep i) (2 * J) (convSquare J g), ?_, hB.norm_sq⟩
  have h1 : (fun p => ((‖transformSum (dyadicStep i) J g p‖ ^ 2 : ℝ) : ℂ)) =
      transformSum (dyadicStep i) (2 * J) (convSquare J g) :=
    funext fun p => (hB.transformSum_convSquare p).symm
  simp only [h1]
  rw [sum_weightedPair]
  refine Submodule.sum_mem _ fun j hj => ?_
  refine stepPairs_le_transformPairs T U i
    (Submodule.subset_span ⟨j, _, hB.convSquare_mem j ?_, rfl⟩)
  have := Finset.mem_range.1 hj
  omega
theorem fst_mem_stripAlgebra {x : (UnitStrip → ℂ) × (H →L[ℂ] H)}
    (hx : x ∈ transformPairs T U) : x.1 ∈ stripAlgebra := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨t, ht, g, hg, rfl⟩ := h
    exact Submodule.subset_span ⟨t, ht, g, hg, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx
theorem exists_snd_of_mem {F : UnitStrip → ℂ} (hF : F ∈ stripAlgebra) :
    ∃ Φ : H →L[ℂ] H, (F, Φ) ∈ transformPairs T U := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨t, ht, g, hg, rfl⟩ := h
    exact ⟨_, Submodule.subset_span ⟨t, ht, g, hg, rfl⟩⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add F G _ _ hF hG =>
    obtain ⟨Φ, hΦ⟩ := hF
    obtain ⟨Ψ, hΨ⟩ := hG
    exact ⟨Φ + Ψ, Submodule.add_mem _ hΦ hΨ⟩
  | smul c F _ hF =>
    obtain ⟨Φ, hΦ⟩ := hF
    exact ⟨c • Φ, Submodule.smul_mem _ c hΦ⟩
variable (T U)
def functionalGraph (v : H) : Submodule ℂ (C₀(UnitStrip, ℂ) × ℂ) where
  carrier := {x | ∃ Φ : H →L[ℂ] H,
    ((x.1 : UnitStrip → ℂ), Φ) ∈ transformPairs T U ∧ x.2 = inner ℂ v (Φ v)}
  zero_mem' := ⟨0, Submodule.zero_mem _, by simp⟩
  add_mem' := by
    rintro x y ⟨Φ, hΦ, hx⟩ ⟨Ψ, hΨ, hy⟩
    refine ⟨Φ + Ψ, Submodule.add_mem _ hΦ hΨ, ?_⟩
    simp [hx, hy]
  smul_mem' := by
    rintro c x ⟨Φ, hΦ, hx⟩
    refine ⟨c • Φ, Submodule.smul_mem _ c hΦ, ?_⟩
    simp [hx]
variable {T U}
theorem exists_positive_functional (hL : SmearingCalculus U)
    (hb : ∀ (τ : ℝ≥0) (J : ℕ) (g : ℕ → ℝ → ℂ), 0 < τ → (∀ j ≤ J, g j ∈ c1Functions) →
      SmearedSumBounds T U τ J g)
    (hA : stripAlgebra ≤ stripC0) (hD : StripAlgebraDense) (v : H) :
    ∃ Λ : C₀(UnitStrip, ℂ) →L[ℂ] ℂ,
      (∀ (F : C₀(UnitStrip, ℂ)) (Φ : H →L[ℂ] H), ((F : UnitStrip → ℂ), Φ) ∈ transformPairs T U →
        Λ F = inner ℂ v (Φ v)) ∧
      (∀ F, ‖Λ F‖ ≤ ‖v‖ ^ 2 * ‖F‖) ∧
      ∀ F : C₀(UnitStrip, ℂ), (∀ y, (F y).im = 0 ∧ 0 ≤ (F y).re) →
        (Λ F).im = 0 ∧ 0 ≤ (Λ F).re := by
  obtain ⟨Λ, hΛ, hbound⟩ := exists_bounded_extension (functionalGraph T U v) (‖v‖ ^ 2)
    (by positivity) (by
      rintro x ⟨Φ, hΦ, hx⟩
      rw [hx]
      have := norm_inner_snd_le hL hb hΦ v
      rw [uniformNorm_eq_norm] at this
      linarith)
  have hval : ∀ (F : C₀(UnitStrip, ℂ)) (Φ : H →L[ℂ] H),
      ((F : UnitStrip → ℂ), Φ) ∈ transformPairs T U → Λ F = inner ℂ v (Φ v) :=
    fun F Φ h => hΛ (F, inner ℂ v (Φ v)) ⟨Φ, h, rfl⟩
  refine ⟨Λ, hval, hbound, fun F hF => ?_⟩
  let S := postcomp (fun z => ((Real.sqrt z.re : ℝ) : ℂ)) (by fun_prop) (by simp) F
  have hS : ∀ y, ((‖S y‖ ^ 2 : ℝ) : ℂ) = F y := by
    intro y
    change ((‖((Real.sqrt (F y).re : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) = F y
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hF y).2]
    apply Complex.ext <;> simp [(hF y).1]
  obtain ⟨Fn, hFn, hlim⟩ := hD S (zeroAtInfty_mem_stripC0 S)
  choose Φ hΦ using fun n => exists_snd_of_mem (T := T) (U := U) (hFn n)
  choose Φ' hΦ' hsq using fun n => exists_normSq_pair hL hb (hΦ n)
  let Q : ℕ → C₀(UnitStrip, ℂ) := fun n => toZeroAtInfty _ (hA (fst_mem_stripAlgebra (hΦ' n)))
  have hQ : ∀ n, Λ (Q n) = ((‖Φ n v‖ ^ 2 : ℝ) : ℂ) := fun n => by
    rw [hval (Q n) (Φ' n) (hΦ' n)]
    exact (hsq n v).symm
  let Fe : ℕ → C₀(UnitStrip, ℂ) := fun n => toZeroAtInfty (Fn n) (hA (hFn n))
  have hδ : Tendsto (fun n => ‖S - Fe n‖) atTop (𝓝 0) := by
    refine hlim.congr fun n => ?_
    exact uniformNorm_eq_norm (S - Fe n)
  have hbd : ∀ n, ‖Q n - F‖ ≤ ‖S - Fe n‖ * (2 * ‖S‖ + ‖S - Fe n‖) := by
    intro n
    refine norm_le_of_forall _ (by positivity) fun y => ?_
    have hQy : Q n y = ((‖Fn n y‖ ^ 2 : ℝ) : ℂ) := rfl
    have h1 : ‖S y - Fe n y‖ ≤ ‖S - Fe n‖ := norm_apply_le_norm (S - Fe n) y
    have h2 : ‖S y‖ ≤ ‖S‖ := norm_apply_le_norm S y
    have h3 : Fe n y = Fn n y := rfl
    change ‖Q n y - F y‖ ≤ _
    rw [hQy, ← hS y, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [h3] at h1
    have h4 : |‖Fn n y‖ - ‖S y‖| ≤ ‖S y - Fn n y‖ := by
      rw [abs_sub_comm]
      exact abs_norm_sub_norm_le _ _
    have h5 : ‖Fn n y‖ ≤ ‖S y‖ + ‖S y - Fn n y‖ := by
      have := (abs_le.1 h4).2
      linarith
    have h6 : ‖Fn n y‖ ^ 2 - ‖S y‖ ^ 2 = (‖Fn n y‖ - ‖S y‖) * (‖Fn n y‖ + ‖S y‖) := by ring
    rw [h6, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖Fn n y‖ + ‖S y‖)]
    have h7 : 0 ≤ ‖S - Fe n‖ := norm_nonneg _
    calc |‖Fn n y‖ - ‖S y‖| * (‖Fn n y‖ + ‖S y‖)
        ≤ ‖S - Fe n‖ * (‖Fn n y‖ + ‖S y‖) := by
          gcongr
          exact h4.trans h1
      _ ≤ ‖S - Fe n‖ * (2 * ‖S‖ + ‖S - Fe n‖) := by
          refine mul_le_mul_of_nonneg_left ?_ h7
          linarith
  have hconv : Tendsto Q atTop (𝓝 F) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hbd ?_
    simpa using hδ.mul ((tendsto_const_nhds (x := 2 * ‖S‖)).add hδ)
  have hΛc := (Λ.continuous.tendsto F).comp hconv
  have him : Tendsto (fun n => (Λ (Q n)).im) atTop (𝓝 (Λ F).im) :=
    (Complex.continuous_im.tendsto _).comp hΛc
  have hre : Tendsto (fun n => (Λ (Q n)).re) atTop (𝓝 (Λ F).re) :=
    (Complex.continuous_re.tendsto _).comp hΛc
  constructor
  · refine tendsto_nhds_unique him ?_
    have h0 : ∀ n, (Λ (Q n)).im = 0 := fun n => by
      rw [hQ]
      exact Complex.ofReal_im _
    simp only [h0]
    exact tendsto_const_nhds
  · refine ge_of_tendsto' hre fun n => ?_
    rw [hQ]
    simp only [Complex.ofReal_re]
    positivity
end Pairs
theorem tendsto_integral_scaledBump_mul (hB : BumpProperties) (h : ℝ → ℂ) (hc : Continuous h)
    (s : ℝ) :
    Tendsto (fun n : ℕ => lebesgueIntegral fun s' => scaledBump (n + 1) s s' * h s') atTop
      (𝓝 (h s)) := by
  obtain ⟨-, -, -, hb, -⟩ := hB
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 hc s (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hmem, hnn, hint, hsupp, -⟩ := hb (n + 1) (by omega) s
  set β := scaledBump (n + 1) s with hβ
  have hβc : Continuous β := hmem.1.continuous
  have hβk : HasCompactSupport β := hmem.2.1
  have hβi : Integrable β := hβc.integrable_of_hasCompactSupport hβk
  have hi1 : Integrable fun s' => β s' * h s' :=
    (hβc.mul hc).integrable_of_hasCompactSupport hβk.mul_right
  have hi2 : Integrable fun s' => β s' * h s := hβi.mul_const _
  have hint' : ∫ s', β s' = 1 := hint
  have e0 : ∫ s', β s' * h s = h s := by rw [integral_mul_const, hint', one_mul]
  have e1 : ∫ s', β s' * (h s' - h s) = (∫ s', β s' * h s') - h s := by
    simp only [mul_sub]
    rw [integral_sub hi1 hi2, e0]
  have hre : ∫ s', (β s').re = 1 := by
    have := Complex.reCLM.integral_comp_comm hβi
    simp only [Complex.reCLM_apply] at this
    rw [this, hint', Complex.one_re]
  have hbi : Integrable fun s' => (β s').re * (ε / 2) :=
    (Complex.reCLM.integrable_comp hβi).mul_const _
  have hbound : ∀ s', ‖β s' * (h s' - h s)‖ ≤ (β s').re * (ε / 2) := by
    intro s'
    by_cases hs : s' ∈ Icc (s - 1 / ((n + 1 : ℕ) : ℝ)) (s + 1 / ((n + 1 : ℕ) : ℝ))
    · have hle : 1 / ((n + 1 : ℕ) : ℝ) < δ := by
        push_cast
        exact lt_of_le_of_lt (Nat.one_div_le_one_div hn) hN
      have hd : dist s' s < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hs.1, hs.2]
      have h1 : ‖h s' - h s‖ ≤ ε / 2 := by
        have := hcont s' hd
        rw [dist_eq_norm] at this
        exact this.le
      have h2 : ‖β s'‖ = (β s').re := by
        have hz : β s' = ((β s').re : ℂ) := by
          apply Complex.ext
          · simp
          · simpa using (hnn s').1
        calc ‖β s'‖ = ‖((β s').re : ℂ)‖ := by rw [← hz]
          _ = (β s').re := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn s').2]
      rw [norm_mul, h2]
      exact mul_le_mul_of_nonneg_left h1 (hnn s').2
    · rw [hsupp s' hs]
      simp
  have hfin : ‖∫ s', β s' * (h s' - h s)‖ ≤ ε / 2 := by
    refine (norm_integral_le_of_norm_le hbi (Eventually.of_forall hbound)).trans (le_of_eq ?_)
    rw [integral_mul_const, hre, one_mul]
  rw [dist_eq_norm]
  change ‖(∫ s', β s' * h s') - h s‖ < ε
  rw [← e1]
  exact lt_of_le_of_lt hfin (half_lt_self hε)
theorem intervalRpow_mem_Icc (t : ℝ≥0) (a : unitInterval) :
    0 ≤ intervalRpow t a ∧ intervalRpow t a ≤ 1 :=
  ⟨Real.rpow_nonneg a.2.1 _, Real.rpow_le_one a.2.1 a.2.2 t.2⟩
section Pair
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ≥0 → H →L[ℂ] H} {U : ℝ → H →L[ℂ] H}
theorem integral_rpow_mul_cexp (hT : SpectralCalculus.IsSelfAdjointContractionSemigroup T)
    (hcm : MatrixCoeffsContinuous T U) (hL : SmearingCalculus U)
    (hB : BumpProperties) (hA : stripAlgebra ≤ stripC0) (v : H)
    {ν : Measure UnitStrip} [IsFiniteMeasure ν] (Λ : C₀(UnitStrip, ℂ) →L[ℂ] ℂ)
    (hval : ∀ (F : C₀(UnitStrip, ℂ)) (Φ : H →L[ℂ] H),
      ((F : UnitStrip → ℂ), Φ) ∈ transformPairs T U → Λ F = inner ℂ v (Φ v))
    (hrep : ∀ F : C₀(UnitStrip, ℂ), Λ F = ∫ y, F y ∂ν)
    {t : ℝ≥0} (ht : t ∈ dyadics) (s : ℝ) :
    ∫ y, (intervalRpow t y.1 : ℂ) * Complex.exp (Complex.I * (s : ℂ) * (y.2 : ℂ)) ∂ν =
      inner ℂ v (T t (U s v)) := by
  have hx : ∀ g ∈ c1Functions,
      ((fun p : UnitStrip => (intervalRpow t p.1 : ℂ) * lineTransform g p.2, T t * smear U g) :
        (UnitStrip → ℂ) × (H →L[ℂ] H)) ∈ transformPairs T U :=
    fun g hg => Submodule.subset_span ⟨t, ht, g, hg, rfl⟩
  have hF : ∀ g ∈ c1Functions,
      (fun p : UnitStrip => (intervalRpow t p.1 : ℂ) * lineTransform g p.2) ∈ stripC0 :=
    fun g hg => hA (fst_mem_stripAlgebra (hx g hg))
  have hv : ∀ g ∈ c1Functions,
      ∫ y, (intervalRpow t y.1 : ℂ) * lineTransform g y.2 ∂ν =
        inner ℂ (T t v) (smear U g v) := by
    intro g hg
    have h1 := hval (toZeroAtInfty _ (hF g hg)) _ (hx g hg)
    rw [hrep] at h1
    refine h1.trans ?_
    exact (hT.isSymmetricBounded t v _).symm
  have hbm := fun n : ℕ => (hB.2.2.2.1 (n + 1) (by omega) s).1
  have hleft : Tendsto
      (fun n : ℕ => ∫ y, (intervalRpow t y.1 : ℂ) * lineTransform (scaledBump (n + 1) s) y.2 ∂ν)
      atTop
      (𝓝 (∫ y, (intervalRpow t y.1 : ℂ) * Complex.exp (Complex.I * (s : ℂ) * (y.2 : ℂ)) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun n => (hF _ (hbm n)).1.aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (intervalRpow_mem_Icc t y.1).1]
      have h1 := (hB.2.2.2.1 (n + 1) (by omega) s).2.2.2.2 y.2
      have h2 := (intervalRpow_mem_Icc t y.1).2
      have h3 := (intervalRpow_mem_Icc t y.1).1
      have h4 := norm_nonneg (lineTransform (scaledBump (n + 1) s) y.2)
      nlinarith
    · exact ((hB.2.2.2.2 s y.2).comp (tendsto_add_atTop_nat 1)).const_mul _
  have hright : Tendsto
      (fun n : ℕ => inner ℂ (T t v) (smear U (scaledBump (n + 1) s) v)) atTop
      (𝓝 (inner ℂ (T t v) (U s v))) := by
    have hcont : Continuous fun s' : ℝ => (inner ℂ (T t v) (U s' v) : ℂ) :=
      continuous_const.inner (hcm.continuous_group v)
    refine (tendsto_integral_scaledBump_mul hB _ hcont s).congr fun n => ?_
    exact (hL.isSmearing _ (hbm n) _ _).symm
  simp only [fun n => hv _ (hbm n)] at hleft
  rw [tendsto_nhds_unique hleft hright]
  exact hT.isSymmetricBounded t v _
theorem continuous_spectralToStrip : Continuous spectralToStrip := by
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_snd
  fun_prop
theorem injective_spectralToStrip : Function.Injective spectralToStrip := by
  intro p p' h
  have h1 : Real.exp (-(p.1 : ℝ)) = Real.exp (-(p'.1 : ℝ)) :=
    congrArg (fun y : UnitStrip => (y.1 : ℝ)) h
  have h2 : (spectralToStrip p).2 = (spectralToStrip p').2 := congrArg Prod.snd h
  exact Prod.ext (NNReal.eq (neg_injective (Real.exp_injective h1))) h2
theorem measurableEmbedding_spectralToStrip : MeasurableEmbedding spectralToStrip :=
  continuous_spectralToStrip.measurableEmbedding injective_spectralToStrip
theorem mem_range_spectralToStrip {y : UnitStrip} (hy : (y.1 : ℝ) ≠ 0) :
    y ∈ range spectralToStrip := by
  have hpos : 0 < (y.1 : ℝ) := lt_of_le_of_ne y.1.2.1 (Ne.symm hy)
  have hlog : 0 ≤ -Real.log (y.1 : ℝ) := neg_nonneg.2 (Real.log_nonpos y.1.2.1 y.1.2.2)
  refine ⟨(⟨-Real.log (y.1 : ℝ), hlog⟩, y.2), Prod.ext (Subtype.ext ?_) rfl⟩
  change Real.exp (-(-Real.log (y.1 : ℝ))) = y.1
  rw [neg_neg, Real.exp_log hpos]
theorem spectralCharacter_eq (t : ℝ≥0) (s : ℝ) (p : SpectralCalculus.SpectralPlane) :
    SpectralCalculus.spectralCharacter t s p =
      (intervalRpow t (spectralToStrip p).1 : ℂ) *
        Complex.exp (Complex.I * (s : ℂ) * ((spectralToStrip p).2 : ℂ)) := by
  have h1 : intervalRpow t (spectralToStrip p).1 = Real.exp (-(t : ℝ) * (p.1 : ℝ)) := by
    simp only [intervalRpow, spectralToStrip]
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [h1, SpectralCalculus.spectralCharacter, Complex.exp_add, Complex.ofReal_exp]
  congr 2
  simp only [spectralToStrip]
  push_cast
  ring
theorem dense_dyadics : Dense dyadics := by
  rw [Metric.dense_iff]
  intro x r hr
  have hlim : Tendsto dyadicStep atTop (𝓝 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by
      rw [inv_lt_one_iff₀]
      right
      norm_num)
  have hlim' : Tendsto (fun i => (dyadicStep i : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (NNReal.continuous_coe.tendsto 0).comp hlim
  obtain ⟨i, hi⟩ := ((tendsto_order.1 hlim').2 r hr).exists
  refine ⟨(⌊(x : ℝ) / dyadicStep i⌋₊ : ℝ≥0) * dyadicStep i, ?_, mul_dyadicStep_mem _ i⟩
  have hd : (0 : ℝ) < dyadicStep i := by exact_mod_cast dyadicStep_pos i
  have h1 : (⌊(x : ℝ) / dyadicStep i⌋₊ : ℝ) ≤ (x : ℝ) / dyadicStep i :=
    Nat.floor_le (by positivity)
  have h2 : (x : ℝ) / dyadicStep i < ⌊(x : ℝ) / dyadicStep i⌋₊ + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hd] at h1
  rw [div_lt_iff₀ hd] at h2
  rw [Metric.mem_ball, NNReal.dist_eq]
  push_cast
  rw [abs_lt]
  constructor <;> nlinarith
theorem exists_measure_spectralPlane (hT : SpectralCalculus.IsSelfAdjointContractionSemigroup T)
    (hU : SpectralCalculus.IsStronglyContinuousUnitaryGroup U) (hcm : MatrixCoeffsContinuous T U)
    (v : H) {ν : Measure UnitStrip} [IsFiniteMeasure ν]
    (hν : ∀ t ∈ dyadics, ∀ s : ℝ,
      ∫ y, (intervalRpow t y.1 : ℂ) * Complex.exp (Complex.I * (s : ℂ) * (y.2 : ℂ)) ∂ν =
        inner ℂ v (T t (U s v))) :
    ∃ m : Measure SpectralCalculus.SpectralPlane, IsFiniteMeasure m ∧ m.real univ = ‖v‖ ^ 2 ∧
      ∀ (t : ℝ≥0) (s : ℝ),
        inner ℂ v (T t (U s v)) = ∫ p, SpectralCalculus.spectralCharacter t s p ∂m := by
  have h0 : (0 : ℝ≥0) ∈ dyadics := ⟨0, 0, by simp⟩
  have hmass : ν.real univ = ‖v‖ ^ 2 := by
    have h1 := hν 0 h0 0
    simp only [intervalRpow, NNReal.coe_zero, Real.rpow_zero, Complex.ofReal_one,
      Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, hT.map_zero, hU.map_zero,
      one_apply_eq_self, integral_const, mul_one] at h1
    rw [inner_self_eq_norm_sq_to_K] at h1
    simp only [Complex.real_smul, mul_one, Complex.coe_algebraMap] at h1
    exact_mod_cast h1
  set Z : Set UnitStrip := {y | (y.1 : ℝ) = 0} with hZ
  have hZm : MeasurableSet Z :=
    (isClosed_eq (continuous_subtype_val.comp continuous_fst) continuous_const).measurableSet
  have hnull : ν Z = 0 := by
    have hle : ∀ i : ℕ, (inner ℂ v (T (dyadicStep i) v) : ℂ).re ≤ ‖v‖ ^ 2 - ν.real Z := by
      intro i
      have h1 := hν _ (mul_dyadicStep_mem 1 i) 0
      simp only [Nat.cast_one, one_mul, Complex.ofReal_zero, mul_zero, zero_mul,
        Complex.exp_zero, mul_one, hU.map_zero, one_apply_eq_self] at h1
      rw [integral_complex_ofReal] at h1
      rw [← h1, Complex.ofReal_re]
      have hcont : Continuous fun y : UnitStrip => intervalRpow (dyadicStep i) y.1 := by
        have : Continuous fun a : unitInterval => intervalRpow (dyadicStep i) a := by
          unfold intervalRpow
          exact continuous_subtype_val.rpow_const fun a =>
            Or.inr (by exact_mod_cast (dyadicStep_pos i).le)
        exact this.comp continuous_fst
      have hi1 : Integrable (fun y : UnitStrip => intervalRpow (dyadicStep i) y.1) ν :=
        Integrable.of_bound hcont.aestronglyMeasurable 1 (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (intervalRpow_mem_Icc _ _).1]
          exact (intervalRpow_mem_Icc _ _).2)
      have hi2 : Integrable (Zᶜ.indicator fun _ : UnitStrip => (1 : ℝ)) ν :=
        (integrable_const _).indicator hZm.compl
      have hmono : ∫ y, intervalRpow (dyadicStep i) y.1 ∂ν ≤
          ∫ y, Zᶜ.indicator (fun _ => (1 : ℝ)) y ∂ν := by
        refine integral_mono hi1 hi2 fun y => ?_
        by_cases hy : y ∈ Z
        · have h2 : (y.1 : ℝ) = 0 := hy
          have h3 : intervalRpow (dyadicStep i) y.1 = 0 := by
            simp only [intervalRpow, h2]
            exact Real.zero_rpow (by exact_mod_cast (dyadicStep_pos i).ne')
          simp [h3, hy]
        · simpa [hy] using (intervalRpow_mem_Icc (dyadicStep i) y.1).2
      rw [integral_indicator_const _ hZm.compl] at hmono
      simp only [smul_eq_mul, mul_one] at hmono
      rw [measureReal_compl hZm, hmass] at hmono
      exact hmono
    have hlim : Tendsto dyadicStep atTop (𝓝 0) :=
      NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by
        rw [inv_lt_one_iff₀]
        right
        norm_num)
    have hTv : Tendsto (fun i => T (dyadicStep i) v) atTop (𝓝 v) := by
      have := ((hcm.continuous_semigroup v).tendsto 0).comp hlim
      simpa [Function.comp_def, hT.map_zero] using this
    have hin : Tendsto (fun i => (inner ℂ v (T (dyadicStep i) v) : ℂ).re) atTop
        (𝓝 (‖v‖ ^ 2)) := by
      have h1 : Tendsto (fun i => (inner ℂ v (T (dyadicStep i) v) : ℂ)) atTop
          (𝓝 (inner ℂ v v)) :=
        tendsto_const_nhds.inner hTv
      have h2 := (Complex.continuous_re.tendsto _).comp h1
      rw [inner_self_eq_norm_sq_to_K] at h2
      simpa [Function.comp_def, ← Complex.ofReal_pow] using h2
    have h3 : ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 - ν.real Z := le_of_tendsto' hin hle
    have h4 : ν.real Z ≤ 0 := by linarith
    have h5 : ν.real Z = 0 := le_antisymm h4 measureReal_nonneg
    exact (measureReal_eq_zero_iff).1 h5
  have me := measurableEmbedding_spectralToStrip
  have hae : ∀ᵐ y ∂ν, y ∈ range spectralToStrip := by
    refine measure_mono_null (fun y hy => ?_) hnull
    by_contra h
    exact hy (mem_range_spectralToStrip h)
  have hmap : (ν.comap spectralToStrip).map spectralToStrip = ν := by
    rw [me.map_comap, Measure.restrict_eq_self_of_ae_mem hae]
  set m := ν.comap spectralToStrip with hm
  have hmu : m univ = ν univ := by
    conv_rhs => rw [← hmap]
    rw [Measure.map_apply me.measurable MeasurableSet.univ, preimage_univ]
  have hfin : IsFiniteMeasure m := ⟨by rw [hmu]; exact measure_lt_top _ _⟩
  have hint : ∀ (t : ℝ≥0) (s : ℝ), ∫ p, SpectralCalculus.spectralCharacter t s p ∂m =
      ∫ y, (intervalRpow t y.1 : ℂ) * Complex.exp (Complex.I * (s : ℂ) * (y.2 : ℂ)) ∂ν := by
    intro t s
    conv_rhs => rw [← hmap]
    rw [me.integral_map]
    exact integral_congr_ae (Eventually.of_forall fun p => spectralCharacter_eq t s p)
  refine ⟨m, hfin, ?_, fun t s => ?_⟩
  · rw [← hmass]
    simp only [Measure.real, hmu]
  · have hbound : ∀ (t : ℝ≥0) (p : SpectralCalculus.SpectralPlane),
        ‖SpectralCalculus.spectralCharacter t s p‖ ≤ 1 := by
      intro t p
      rw [SpectralCalculus.spectralCharacter, Complex.norm_exp]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
        Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, add_zero]
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (t : ℝ) * (p.1 : ℝ) := mul_nonneg t.2 p.1.2
      nlinarith
    have hc1 : Continuous fun t : ℝ≥0 =>
        ∫ p, SpectralCalculus.spectralCharacter t s p ∂m := by
      refine continuous_of_dominated (bound := fun _ => 1) (fun t => ?_)
        (fun t => Eventually.of_forall (hbound t)) (integrable_const _)
        (Eventually.of_forall fun p => ?_)
      · refine Continuous.aestronglyMeasurable ?_
        unfold SpectralCalculus.spectralCharacter
        fun_prop
      · unfold SpectralCalculus.spectralCharacter
        fun_prop
    have hc2 : Continuous fun t : ℝ≥0 => (inner ℂ v (T t (U s v)) : ℂ) :=
      continuous_const.inner (hcm.continuous_semigroup _)
    have heq := Continuous.ext_on dense_dyadics hc2 hc1 (fun t ht => by
      rw [hint, hν t ht s])
    exact congrFun heq t
end Pair
end YangMills.Construction.TwoPoints.LineTransforms.VectorMeasure
namespace YangMills.Construction.SpectralCalculus
open TwoPoints.LineTransforms TwoPoints.LineTransforms.VectorMeasure in
theorem vectorSpectralMeasureExists_of_lineTransforms
    (h₁ : TwoPoints.LineTransforms.SmearedPairBounds)
    (h₂ : TwoPoints.LineTransforms.ConvPowDensity.Statement) :
    VectorSpectralMeasureExists := by
  intro H _ _ _ T U hc v
  obtain ⟨hcm, hL, -, hb⟩ := h₁ H T U hc
  obtain ⟨-, -, -, -, hB, ⟨hA, -⟩, hD⟩ := h₂
  obtain ⟨Λ, hval, hbound, hpos⟩ := exists_positive_functional hL
    (fun τ J g hτ hg => hb τ J g hτ hg) hA hD v
  obtain ⟨ν, hfin, hrep⟩ := exists_finiteMeasure_rep Λ (‖v‖ ^ 2) (by positivity) hbound hpos
  exact exists_measure_spectralPlane hc.semigroup hc.group hcm v
    fun t ht s => integral_rpow_mul_cexp hc.semigroup hcm hL hB hA v Λ hval hrep ht s
end YangMills.Construction.SpectralCalculus
end
