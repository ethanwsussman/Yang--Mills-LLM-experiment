import YangMills.Construction.FreeEnergiesOfTheFlow.FittedResponsesAreMeansProof
import YangMills.Construction.LawOnABoxOfTheFlow.AxialGaugeOfAColdFilling
import YangMills.Construction.LawOnABoxOfTheFlow.BackgroundFromItsBlockMeans
import YangMills.Construction.LawOnABoxOfTheFlow.BorelBackgroundOfAFilling
import YangMills.Construction.LawOnABoxOfTheFlow.BorelFillingOfTheOutside
import YangMills.Construction.LawOnABoxOfTheFlow.ChartOverAFrame
import YangMills.Construction.LawOnABoxOfTheFlow.ColdEventsOfABoxAreLikely
import YangMills.Construction.LawOnABoxOfTheFlow.ColdFieldsLieInTheChart
import YangMills.Construction.LawOnABoxOfTheFlow.DrawsBelowATopHaveTheirLaw
import YangMills.Construction.LawOnABoxOfTheFlow.DrawsHaveTheirBases
import YangMills.Construction.LawOnABoxOfTheFlow.LawOnABox
import YangMills.Construction.LawOnABoxOfTheFlow.MeanUnderAnEventOfGaussianMass
import YangMills.Construction.LawOnABoxOfTheFlow.OutsideValuesOfABox
import YangMills.Construction.LawOnABoxOfTheFlow.SizesOfTheBackground
import YangMills.Construction.LawOnABoxOfTheFlow.ToolsOfAChart
import YangMills.Construction.LawOnABoxOfTheFlow.WeightsOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps RenormalizationStepParameters StepSettings WeightedResponses ResponseInTheExpansion BlockAverages BoxEvents
set_option synthInstance.maxSize 1024
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
private theorem exists_threshold_boxRadius {κ₀ : ℝ} (h1 : 1 / 27 ≤ κ₀) (h2 : κ₀ ≤ 1 / 21) (r₁ : ℕ) (a Ce K : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      3 ≤ x ∧ r₁ ≤ boxRadius κ₀ x ∧ 32 * (boxRadius κ₀ x : ℝ) ≤ x ^ (1 / 10 : ℝ) ∧ a ≤ x ^ (1 / 10 : ℝ) ∧
      Ce * ((boxRadius κ₀ x : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) ≤ 1 / 100 ∧ K ≤ Real.log x := by
  set Ce' : ℝ := |Ce| * (512 * 84 ^ 3) with hCe'
  set U : ℝ := max (max 4 ((r₁ : ℝ) + 1)) (max (|a| + 1) (100 * Ce' + 1)) with hU
  have hU4 : 4 ≤ U := le_trans (le_max_left _ _) (le_max_left _ _)
  have hUr : (r₁ : ℝ) + 1 ≤ U := le_trans (le_max_right _ _) (le_max_left _ _)
  have hUa : |a| + 1 ≤ U := le_trans (le_max_left _ _) (le_max_right _ _)
  have hUc : 100 * Ce' + 1 ≤ U := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨max (U ^ 84) (Real.exp K), fun x hx => ?_⟩
  have hxU : U ^ 84 ≤ x := le_trans (le_max_left _ _) hx
  have hxK : Real.exp K ≤ x := le_trans (le_max_right _ _) hx
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hx1 : 1 ≤ x := le_trans (one_le_pow₀ hU1) hxU
  have hx0 : 0 < x := by linarith
  set u : ℝ := x ^ (1 / 84 : ℝ) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hx0 _
  have huU : U ≤ u := by
    calc U = (U ^ (84 : ℕ)) ^ (1 / 84 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
          norm_num
      _ ≤ u := Real.rpow_le_rpow (by positivity) hxU (by norm_num)
  have hu1 : 1 ≤ u := by linarith
  have hpow : ∀ m : ℕ, x ^ ((m : ℝ) / 84) = u ^ m := by
    intro m
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  set R := boxRadius κ₀ x with hR
  have hRle : (R : ℝ) ≤ 2 * u ^ 4 := by
    have h3 : (R : ℝ) < x ^ κ₀ + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le _)
    have h4 : x ^ κ₀ ≤ u ^ 4 := by
      rw [← hpow 4]
      refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
      norm_num
      linarith
    have h5 : (1 : ℝ) ≤ u ^ 4 := one_le_pow₀ hu1
    linarith
  have hRge : u ^ 3 ≤ (R : ℝ) := by
    have h3 : x ^ κ₀ ≤ (R : ℝ) := Nat.le_ceil _
    refine le_trans ?_ h3
    rw [← hpow 3]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    norm_num
    linarith
  have h10 : u ^ 8 ≤ x ^ (1 / 10 : ℝ) := by
    rw [← hpow 8]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    norm_num
  have hu3 : u ≤ u ^ 3 := by
    calc u = u ^ 1 := (pow_one _).symm
      _ ≤ u ^ 3 := pow_le_pow_right₀ hu1 (by norm_num)
  have hu8 : u ≤ u ^ 8 := by
    calc u = u ^ 1 := (pow_one _).symm
      _ ≤ u ^ 8 := pow_le_pow_right₀ hu1 (by norm_num)
  have hlog : Real.log x ≤ 84 * u := by
    have := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 84 by norm_num)
    calc Real.log x ≤ u / (1 / 84) := this
      _ = 84 * u := by ring
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hinv : x ^ (-(1 / 2 : ℝ)) = (u ^ 42)⁻¹ := by
    rw [Real.rpow_neg hx0.le, ← hpow 42]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (3 : ℝ) ≤ U ^ 84 := by
      calc (3 : ℝ) ≤ U := by linarith
        _ = U ^ 1 := (pow_one _).symm
        _ ≤ U ^ 84 := pow_le_pow_right₀ hU1 (by norm_num)
    linarith
  · have : (r₁ : ℝ) ≤ (R : ℝ) := by linarith
    exact_mod_cast this
  · have h4 : (4 : ℝ) ≤ u := by linarith
    have h5 : (64 : ℝ) ≤ u ^ 4 := by
      calc (64 : ℝ) ≤ 4 ^ 4 := by norm_num
        _ ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) h4 4
    have h6 : (0 : ℝ) ≤ u ^ 4 := by positivity
    calc 32 * (R : ℝ) ≤ 32 * (2 * u ^ 4) := by linarith
      _ = 64 * u ^ 4 := by ring
      _ ≤ u ^ 4 * u ^ 4 := mul_le_mul_of_nonneg_right h5 h6
      _ = u ^ 8 := by ring
      _ ≤ _ := h10
  · have : a ≤ |a| := le_abs_self a
    linarith
  · have hmain : (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3 ≤ 512 * 84 ^ 3 * (u ^ 3)⁻¹ := by
      have h3 : (R : ℝ) ^ 9 ≤ (2 * u ^ 4) ^ 9 := pow_le_pow_left₀ (by positivity) hRle 9
      have h4 : Real.log x ^ 3 ≤ (84 * u) ^ 3 := pow_le_pow_left₀ hlog0 hlog 3
      rw [hinv]
      calc (R : ℝ) ^ 9 * (u ^ 42)⁻¹ * Real.log x ^ 3 ≤ (2 * u ^ 4) ^ 9 * (u ^ 42)⁻¹ * (84 * u) ^ 3 := by
            gcongr
        _ = 512 * 84 ^ 3 * (u ^ 3)⁻¹ := by
            field_simp
            ring
    have ht : 0 ≤ (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3 := by
      have : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
      positivity
    have hCe : Ce ≤ |Ce| := le_abs_self _
    have h100 : Ce' * (u ^ 3)⁻¹ ≤ 1 / 100 := by
      have hu3p : 0 < u ^ 3 := by positivity
      rw [← div_eq_mul_inv, div_le_iff₀ hu3p]
      have : 100 * Ce' ≤ u ^ 3 := by linarith
      linarith
    calc Ce * ((R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3)
        ≤ |Ce| * ((R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) := mul_le_mul_of_nonneg_right hCe ht
      _ ≤ |Ce| * (512 * 84 ^ 3 * (u ^ 3)⁻¹) := mul_le_mul_of_nonneg_left hmain (abs_nonneg _)
      _ = Ce' * (u ^ 3)⁻¹ := by
          simp only [hCe']
          ring
      _ ≤ 1 / 100 := h100
  · rw [Real.le_log_iff_exp_le hx0]
    exact hxK
private theorem gaussianMass_ge_of_weightedLaw {V : Type} [MeasurableSpace V] {γ : Measure V} [IsProbabilityMeasure γ]
    {ell E : Set V} (hell : MeasurableSet ell) (hE : MeasurableSet E) {w : V → ℝ} (hw : Measurable w) {ε η : ℝ}
    (hε : 0 ≤ ε) (hb : ∀ ζ ∈ ell, 0 < w ζ ∧ |Real.log (w ζ)| ≤ ε) (hm : 1 - η ≤ γ.real ell) (hη : η < 1)
    (hnum : 0.6 ≤ 0.65 * Real.exp (-(2 * ε)) * (1 - η))
    (hlaw : ENNReal.ofReal 0.65 ≤ normalize ((γ.restrict ell).withDensity fun ζ => ENNReal.ofReal (w ζ)) E) :
    0.6 ≤ γ.real (E ∩ ell) := by
  set f : V → ENNReal := fun ζ => ENNReal.ofReal (w ζ) with hf
  set g₁ := γ.real (E ∩ ell) with hg₁
  set g₂ := γ.real ell with hg₂
  have hg₂0 : 0 < g₂ := by linarith
  have hbd : ∀ ζ ∈ ell, f ζ ≤ ENNReal.ofReal (Real.exp ε) ∧ ENNReal.ofReal (Real.exp (-ε)) ≤ f ζ := by
    intro ζ hζ
    obtain ⟨a1, a2⟩ := hb ζ hζ
    have a3 := abs_le.1 a2
    refine ⟨ENNReal.ofReal_le_ofReal ?_, ENNReal.ofReal_le_ofReal ?_⟩
    · calc w ζ = Real.exp (Real.log (w ζ)) := (Real.exp_log a1).symm
        _ ≤ Real.exp ε := Real.exp_le_exp.2 a3.2
    · calc Real.exp (-ε) ≤ Real.exp (Real.log (w ζ)) := Real.exp_le_exp.2 a3.1
        _ = w ζ := Real.exp_log a1
  have hγ₁ : γ (E ∩ ell) = ENNReal.ofReal g₁ := by
    rw [hg₁, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hγ₂ : γ ell = ENNReal.ofReal g₂ := by
    rw [hg₂, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hup : ((γ.restrict ell).withDensity f) E ≤ ENNReal.ofReal (Real.exp ε * g₁) := by
    rw [withDensity_apply _ hE, Measure.restrict_restrict hE]
    calc ∫⁻ ζ in E ∩ ell, f ζ ∂γ ≤ ∫⁻ ζ in E ∩ ell, ENNReal.ofReal (Real.exp ε) ∂γ :=
          setLIntegral_mono' (hE.inter hell) fun ζ hζ => (hbd ζ hζ.2).1
      _ = ENNReal.ofReal (Real.exp ε * g₁) := by
          rw [setLIntegral_const, hγ₁, ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hlow : ENNReal.ofReal (Real.exp (-ε) * g₂) ≤ ((γ.restrict ell).withDensity f) Set.univ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ENNReal.ofReal (Real.exp (-ε) * g₂) = ∫⁻ ζ in ell, ENNReal.ofReal (Real.exp (-ε)) ∂γ := by
          rw [setLIntegral_const, hγ₂, ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ∫⁻ ζ in ell, f ζ ∂γ := setLIntegral_mono' hell fun ζ hζ => (hbd ζ hζ).2
  have hlp : 0 < Real.exp (-ε) * g₂ := by positivity
  have h3 : ENNReal.ofReal 0.65 ≤ ENNReal.ofReal (Real.exp ε * g₁ / (Real.exp (-ε) * g₂)) := by
    refine le_trans hlaw ?_
    unfold normalize
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_div_of_pos hlp, div_eq_mul_inv, mul_comm]
    exact mul_le_mul' hup (ENNReal.inv_le_inv.2 hlow)
  have h4 : (0.65 : ℝ) ≤ Real.exp ε * g₁ / (Real.exp (-ε) * g₂) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  rw [le_div_iff₀ hlp] at h4
  have h5 : 0.65 * Real.exp (-(2 * ε)) * g₂ ≤ g₁ := by
    have e1 : Real.exp (-(2 * ε)) = Real.exp (-ε) * (Real.exp ε)⁻¹ := by
      rw [← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    rw [e1]
    calc 0.65 * (Real.exp (-ε) * (Real.exp ε)⁻¹) * g₂ = (0.65 * (Real.exp (-ε) * g₂)) * (Real.exp ε)⁻¹ := by ring
      _ ≤ (Real.exp ε * g₁) * (Real.exp ε)⁻¹ := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = g₁ := by field_simp
  have h6 : 0.65 * Real.exp (-(2 * ε)) * (1 - η) ≤ 0.65 * Real.exp (-(2 * ε)) * g₂ :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  linarith
section Restriction
variable {ℓ : StepParameters} {n : ℕ} [NeZero n] {T : StageTower ℓ} {k : ℕ} {o : TorusSite n} {R : ℕ}
private def restrictChart (c : BoxChart T k o R) (G : Set (OuterData T k o R)) : BoxChart T k o R :=
  { c with goodOuter := G, orbitSet := c.orbitSet ∩ (Prod.fst ⁻¹' G) }
private theorem restrictChart_isMeasurable {c : BoxChart T k o R} (hc : c.IsMeasurable) {G : Set (OuterData T k o R)}
    (hG : MeasurableSet G) (hsub : G ⊆ c.goodOuter) : (restrictChart c G).IsMeasurable := by
  have hι : Measurable fun q : G => (⟨q.1, hsub q.2⟩ : c.goodOuter) :=
    Measurable.subtype_mk measurable_subtype_coe
  have hι' : Measurable fun p : (restrictChart c G).orbitSet => (⟨p.1, p.2.1⟩ : c.orbitSet) :=
    Measurable.subtype_mk measurable_subtype_coe
  exact
    { measurableSet_goodOuter := hG
      measurableSet_orbitSet := hc.measurableSet_orbitSet.inter (measurable_fst hG)
      fst_mem_goodOuter := fun p hp => hp.2
      measurable_axialGauge := hc.measurable_axialGauge.comp hι
      measurable_background := hc.measurable_background.comp hι
      measurable_coord := hc.measurable_coord.comp hι'
      measurable_weight := hc.measurable_weight.comp ((hι.comp measurable_fst).prodMk measurable_snd)
      measurable_meanCurl := hc.measurable_meanCurl.comp hι
      gauge_mem := fun p hp γ hγ => ⟨hc.gauge_mem p hp.1 γ hγ, hp.2⟩ }
private theorem restrictChart_isInGauge {c : BoxChart T k o R} {C δ c₀ : ℝ} (h : c.IsInGauge C δ c₀)
    (G : Set (OuterData T k o R)) : (restrictChart c G).IsInGauge C δ c₀ :=
  ⟨fun p hp => h.mem_chart p hp.1, fun p hp => h.coord_unique p hp.1, fun p hp => h.bounds p hp.1⟩
private theorem restrictChart_hasLaw {c : BoxChart T k o R} {P : Measure (MarkedSample ℓ k n)} {x c₀ ε : ℝ}
    (h : c.HasLaw P x c₀ ε) {G : Set (OuterData T k o R)} (hG : MeasurableSet G) (hsub : G ⊆ c.goodOuter)
    (he : Measurable fun u => outerData T k o R (stageState T k n u)) :
    (restrictChart c G).HasLaw P x c₀ ε := by
  classical
  refine ⟨fun F hF hFb => ?_, fun q hq ζ hζ => h.weight_bounds q (hsub hq) ζ hζ,
    fun q hq => h.ellipsoid_mass q (hsub hq)⟩
  obtain ⟨Mb, hMb⟩ := hFb
  let D : Set (MarkedSample ℓ k n) := {u | outerData T k o R (stageState T k n u) ∈ G}
  have hD : MeasurableSet D := he hG
  let F' : OuterData T k o R × (TorusBond n → imaginaryQuaternions) → ℝ := (Prod.fst ⁻¹' G).indicator F
  have hF' : Measurable F' := hF.indicator (measurable_fst hG)
  have hb' : ∃ M : ℝ, ∀ z, |F' z| ≤ M := by
    refine ⟨max Mb 0, fun z => ?_⟩
    by_cases hz : z ∈ Prod.fst ⁻¹' G
    · simp only [F', Set.indicator_of_mem hz]
      exact le_trans (hMb z) (le_max_left _ _)
    · simp only [F', Set.indicator_of_notMem hz, abs_zero]
      exact le_max_right _ _
  have h0 := h.integral_eq F' hF' hb'
  have hev : (restrictChart c G).event = c.event ∩ D := rfl
  rw [hev, ← setIntegral_indicator hD, ← setIntegral_indicator hD]
  have e1 : ∀ u, D.indicator (fun u => F (outerData T k o R (stageState T k n u),
      (restrictChart c G).coord (outerData T k o R (stageState T k n u)) (restrictInner o R (stageState T k n u).1))) u =
      F' (outerData T k o R (stageState T k n u),
        c.coord (outerData T k o R (stageState T k n u)) (restrictInner o R (stageState T k n u).1)) := by
    intro u
    by_cases hu : u ∈ D
    · rw [Set.indicator_of_mem hu]
      exact (Set.indicator_of_mem (show (_, _) ∈ Prod.fst ⁻¹' G from hu) _).symm
    · rw [Set.indicator_of_notMem hu]
      exact (Set.indicator_of_notMem (show (_, _) ∉ Prod.fst ⁻¹' G from hu) _).symm
  have e2 : ∀ u, D.indicator (fun u => ∫ ζ, F (outerData T k o R (stageState T k n u), ζ)
      ∂((restrictChart c G).coordLaw x c₀ (outerData T k o R (stageState T k n u)))) u =
      ∫ ζ, F' (outerData T k o R (stageState T k n u), ζ)
        ∂(c.coordLaw x c₀ (outerData T k o R (stageState T k n u))) := by
    intro u
    by_cases hu : u ∈ D
    · rw [Set.indicator_of_mem hu]
      refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
      exact (Set.indicator_of_mem (show (_, ζ) ∈ Prod.fst ⁻¹' G from hu) _).symm
    · rw [Set.indicator_of_notMem hu]
      have : ∀ ζ, F' (outerData T k o R (stageState T k n u), ζ) = 0 := fun ζ =>
        Set.indicator_of_notMem (show (_, ζ) ∉ Prod.fst ⁻¹' G from hu) _
      simp only [this, integral_zero]
  simp only [e1, e2]
  exact h0
private theorem isInGauge_mono {c : BoxChart T k o R} {C C' δ c₀ : ℝ} (hC : C ≤ C') (hδ : 0 ≤ δ)
    (h : c.IsInGauge C δ c₀) : c.IsInGauge C' δ c₀ := by
  have hm : ∀ (e : ℕ) (d : ℝ), 0 ≤ d → C * (R : ℝ) ^ e * d ≤ C' * (R : ℝ) ^ e * d := fun e d hd =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) hd
  refine ⟨h.mem_chart, h.coord_unique, fun p hp => ?_⟩
  obtain ⟨γ, v, β, hγ, h1, h2, h3, h4⟩ := h.bounds p hp
  refine ⟨γ, v, β, hγ, fun b hb => ?_, h2.trans (hm 6 _ (by positivity)), fun q hq => (h3 q hq).trans (hm 2 _ hδ),
    h4.trans (hm 4 _ (by positivity))⟩
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1 b hb
  exact ⟨a1, a2, a3, a4.trans (hm 3 _ hδ), a5.trans (hm 3 _ hδ), a6.trans (hm 3 _ hδ)⟩
private theorem stageState_fst_eq_topField {ℓ : StepParameters} (T : StageTower ℓ) (k n : ℕ) [NeZero n]
    (u : MarkedSample ℓ k n) : (stageState T k n u).1 = topField ℓ k n u := by apply _root_.YangMills.SharedProofs.p2480 <;> assumption
end Restriction
private theorem measurable_restrictedCurl_of_finset {n : ℕ} [NeZero n] (S : Finset (TorusSite n)) :
    Measurable fun v : TorusBond n → imaginaryQuaternions => restrictedCurl S v := by
  classical
  refine Continuous.measurable (continuous_pi fun p => ?_)
  by_cases h : p ∈ plaquettesIn S
  · simp only [restrictedCurl, if_pos h]
    exact continuous_lieFormCurl p
  · simp only [restrictedCurl, if_neg h]
    exact continuous_const
private theorem measurable_ite_mem_of_restrict {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {F : Set α}
    (hF : MeasurableSet F) {f : α → β} (hf : Measurable fun u : F => f u) (b : β) [DecidablePred (· ∈ F)] :
    Measurable fun u => if u ∈ F then f u else b := by
  refine measurable_of_restrict_of_restrict_compl hF ?_ ?_
  · have e : F.domRestrict (fun u => if u ∈ F then f u else b) = fun u : F => f u := by
      funext u
      show (if (u : α) ∈ F then f u else b) = f u
      rw [if_pos u.2]
    rw [e]
    exact hf
  · have e : Fᶜ.domRestrict (fun u => if u ∈ F then f u else b) = fun _ => b := by
      funext u
      show (if (u : α) ∈ F then f u else b) = b
      rw [if_neg u.2]
    rw [e]
    exact measurable_const
set_option maxHeartbeats 4000000 in
theorem boxGaussianLaw_of_components (hFrame : chartOverFrameStatement) (hOut : goodOuterDataStatement)
    (hCold : coldEventsLikelyStatement) (hDr : sampleBelowLawStatement)
    (hCirc : circulationBoundStatement) (hBases : ae_hasBaseChoicesStatement)
    (hCF : coldFieldsInChartStatement) (hAx : coldAxialGaugeStatement)
    (hFill : borelOuterFillingStatement) (hBack : borelBackgroundStatement)
    (hSize : backgroundCurlBoundsStatement) (hMean : criticalCurlBoundFromLargeEventStatement)
    (hBlock : backgroundFromBlockMeansStatement) (hWts : blockWeightBoundsStatement)
    (hKer : curlCovarianceBoundsStatement) (hSt : StageStatesMeasurableStatement) :
    boxGaussianLawStatement := by
  refine holdsAtAdmissibleParameters_mono ?_ (holdsAtAdmissibleParameters_and hFrame (holdsAtAdmissibleParameters_and hOut
    (holdsAtAdmissibleParameters_and hCold (holdsAtAdmissibleParameters_and hDr (holdsAtAdmissibleParameters_and hCirc
    (holdsAtAdmissibleParameters_and hSize holdsAtAdmissibleParameters_floorMin_le))))))
  rintro Tb y hTb ⟨hfr, hou, hco, hdr, hci, hsi, hy₀⟩ κ₀ h1 h2
  haveI : NeZero Tb.side := ⟨by have := hTb.L_ge; omega⟩
  have hL40 : 2 ^ 40 ≤ Tb.side := hTb.L_ge
  have hLodd : Odd Tb.side := hTb.L_odd
  have hLeq : (Tb.stepParameters y).side = Tb.side := rfl
  obtain ⟨C₁, hfr'⟩ := hfr κ₀ h1 h2
  obtain ⟨C₀c, xcf, hC₀c, hcf⟩ := hCF Tb hTb κ₀ h1 h2
  set C₀ : ℝ := max (max C₁ C₀c) 1 with hC₀
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨Cf, xf, hfr''⟩ := hfr' C₀ (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨xo, xpo, hou'⟩ := hou κ₀ h1 h2
  obtain ⟨xc, xpc, hco'⟩ := hco κ₀ h1 h2
  obtain ⟨xi, hci'⟩ := hci κ₀ h1 h2 C₀ hC₀pos
  obtain ⟨Cb, xb, hbk⟩ := hBack Tb hTb κ₀ h1 h2
  obtain ⟨Cs, xsz, Cj, hsz⟩ := hsi κ₀ h1 h2 (max Cb 0) (le_max_right _ _)
  obtain ⟨Km, xm, hmn⟩ := hMean Tb hTb κ₀ h1 h2
  obtain ⟨Cbl, Rbl, hblk⟩ := hBlock Tb.side hLodd (by omega) (Cj 2)
  obtain ⟨xa, hax⟩ := hAx κ₀ h1 h2
  obtain ⟨Rk, hker⟩ := hKer Tb hTb
  set r₁ : ℕ := max (max Rk Rbl) ((2 ^ 8 * Tb.side) ^ 3 + 2) with hr₁
  set Cc : ℝ := max (max (max Cf Cs) Cbl) ((2 * Tb.coercivity)⁻¹) with hCc
  obtain ⟨Xn, hXn⟩ := exists_threshold_boxRadius h1 h2 r₁ ((Tb.side : ℝ) * (Tb.n₀ : ℝ)) Cf (|Km| + 1)
  refine ⟨Cc, C₀, max Xn (max (max (max xf xo) (max xc xi)) (max (max xb xsz) (max xm (max xa xcf)))), Cj,
    fun p => max (xpo (p + 1)) (xpc (p + 1)), ?_⟩
  intro T β k n _ o x R hdat hx hR
  set xs := max Xn (max (max (max xf xo) (max xc xi)) (max (max xb xsz) (max xm (max xa xcf)))) with hxs
  have hfl : xs ≤ x := by rw [hx]; exact hdat.le_coupling
  have hxn : Xn ≤ x := le_trans (le_max_left _ _) hfl
  have hrest : max (max (max xf xo) (max xc xi)) (max (max xb xsz) (max xm (max xa xcf))) ≤ x :=
    le_trans (le_max_right _ _) hfl
  have hA1 := le_trans (le_max_left _ _) hrest
  have hA2 := le_trans (le_max_right _ _) hrest
  have hxf : xf ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA1
  have hxo : xo ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA1
  have hxc : xc ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA1
  have hxi : xi ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hA1
  have hxb : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA2
  have hxsz : xsz ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA2
  have hxm : xm ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA2
  have hxa : xa ≤ x := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hA2
  have hxcf : xcf ≤ x := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hA2
  obtain ⟨hx3, hRr₁, h32, hLn, hεs, hKlog⟩ := hXn x hxn
  rw [← hR] at hRr₁ h32 hεs
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hRk : Rk ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hRr₁
  have hRbl : Rbl ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hRr₁
  have hR3 : (2 ^ 8 * Tb.side) ^ 3 + 2 ≤ R := le_trans (le_max_right _ _) hRr₁
  have hR2 : 2 ≤ R := by omega
  have hRpos : (1 : ℝ) ≤ R := by
    have : 1 ≤ R := by omega
    exact_mod_cast this
  have hwide : x ^ (1 / 10 : ℝ) ≤ (n : ℝ) := by rw [hx]; exact hdat.coupling_rpow_le
  have h16 : 16 * R < n := by
    have : (16 * (R : ℝ)) < n := by linarith
    exact_mod_cast this
  have hLn' : ((Tb.side * Tb.n₀ : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    linarith
  have hLn'' : Tb.side * Tb.n₀ ≤ n := by exact_mod_cast hLn'
  set s := coarseningSteps Tb.side R with hs
  have hLr : (2 : ℝ) ≤ (Tb.side : ℝ) := by
    have : 2 ≤ Tb.side := by omega
    exact_mod_cast this
  have hR23 : (R : ℝ) ^ (2 / 3 : ℝ) ≤ (R : ℝ) := by
    calc (R : ℝ) ^ (2 / 3 : ℝ) ≤ (R : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hRpos (by norm_num)
      _ = R := Real.rpow_one _
  have hset : {s : ℕ | (R : ℝ) ^ (2 / 3 : ℝ) ≤ (Tb.side : ℝ) ^ s}.Nonempty := by
    refine ⟨R, ?_⟩
    show (R : ℝ) ^ (2 / 3 : ℝ) ≤ (Tb.side : ℝ) ^ R
    refine le_trans hR23 ?_
    have : R < Tb.side ^ R := Nat.lt_pow_self (by omega)
    exact_mod_cast this.le
  have hsmem : (R : ℝ) ^ (2 / 3 : ℝ) ≤ (Tb.side : ℝ) ^ s := Nat.sInf_mem hset
  have hRgt : (1 : ℝ) < (R : ℝ) ^ (2 / 3 : ℝ) := by
    have : (1 : ℝ) < R := by
      have h3 : 1 < R := by omega
      exact_mod_cast h3
    exact Real.one_lt_rpow this (by norm_num)
  have hs1 : 1 ≤ s := by
    by_contra hcon
    have h0 : s = 0 := by omega
    rw [h0, pow_zero] at hsmem
    linarith
  have hsm : (Tb.side : ℝ) ^ (s - 1) < (R : ℝ) ^ (2 / 3 : ℝ) := by
    have := Nat.notMem_of_lt_sInf (show s - 1 < sInf {s : ℕ | (R : ℝ) ^ (2 / 3 : ℝ) ≤ (Tb.side : ℝ) ^ s} by
      show s - 1 < s
      omega)
    simpa using this
  obtain ⟨e, he⟩ := hdat.side_eq
  have hLe : (Tb.stepParameters y).side = Tb.side := rfl
  rw [hLe] at he
  have hse : s ≤ e := by
    by_contra hcon
    have h3 : e ≤ s - 1 := by omega
    have h4 : (Tb.side : ℝ) ^ e ≤ (Tb.side : ℝ) ^ (s - 1) := pow_le_pow_right₀ (by linarith) h3
    have h5 : (n : ℝ) = 2 * (Tb.side : ℝ) ^ e := by rw [he]; push_cast; ring
    have h6 : (16 * R : ℝ) < n := by exact_mod_cast h16
    nlinarith
  set n' := 2 * Tb.side ^ (e - s) with hn'
  have hn'0 : n' ≠ 0 := by
    have : 0 < Tb.side := by omega
    positivity
  haveI : NeZero n' := ⟨hn'0⟩
  have hnn : n = fineSide Tb.side s n' := by
    rw [fineSide_eq, he, hn', mul_assoc, ← pow_add, Nat.sub_add_cancel hse]
  have hsR : s = coarseningSteps (Tb.stepParameters y).side R := rfl
  have hbs : IsBlockTorusSide (Tb.stepParameters y) n := by
    refine ⟨?_, hLn''⟩
    show Tb.side ∣ n
    rw [he]
    exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
  subst hnn
  have hRL : fineSide Tb.side s n' = fineSide (Tb.stepParameters y).side s n' := rfl
  set δ := boxScale x with hδ
  set c₀ := C₀ * (R : ℝ) ^ 4 * δ ^ 2 with hc₀
  set S := supBall o (2 * (R : ℝ)) with hS
  have hδ0 : 0 ≤ δ := by
    have : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h3 : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
    simp only [hδ, boxScale]
    positivity
  have hdatum : ∀ {xs' : ℝ}, xs' ≤ x → IsBoxDatum Tb y T β κ₀ xs' k (fineSide Tb.side s n') := fun h =>
    ⟨by rw [← hx]; exact h, hdat.onFamily, hdat.measurable, hdat.side_eq, hdat.coupling_rpow_le⟩
  have hst' : IsTowerAtParameters Tb y T β (k + s) := by
    have h3 := hdat.onFamily
    rw [← hx, ← hR] at h3
    exact h3
  have hst : IsTowerAtParameters Tb y T β k :=
    ⟨hst'.startsAtWilson, fun j hj => hst'.coupling_eq j (by omega), fun j hj => hst'.onFamily j (by omega)⟩
  have hyj : ∀ j ≤ k + s, y ≤ flowCoupling (Tb.stepParameters y) β j := fun j hj => by
    have h3 := (hst'.onFamily j hj).le_coupling
    have h4 := hst'.coupling_eq j (by omega)
    show y ≤ (couplingFlow (Tb.stepParameters y) β j).1
    rw [← h4]
    exact h3
  obtain ⟨hP'p, hmap⟩ := hdr T β k s n' hst' hdat.measurable hyj
  haveI := hP'p
  haveI hPp : IsProbabilityMeasure (markedSampleLaw T β k (fineSide Tb.side s n')) :=
    (hdr T β k 0 (fineSide Tb.side s n') hst hdat.measurable fun j hj => hyj j (by omega)).1
  have hfit : (Tb.stepParameters y).Admissible := hTb.fits y hy₀
  have hstate : Measurable (stageState T k (fineSide Tb.side s n')) := hSt _ hfit T k _
  let e₁ : MarkedSample (Tb.stepParameters y) k (fineSide Tb.side s n') → OuterData T k o R :=
    fun u => outerData T k o R (stageState T k _ u)
  let e₂ : MarkedSample (Tb.stepParameters y) k (fineSide Tb.side s n') → InnerField o R :=
    fun u => restrictInner o R (stageState T k _ u).1
  have he₁ : Measurable e₁ :=
    ((measurable_restrictOuter o R).comp (measurable_fst.comp hstate)).prodMk (measurable_snd.comp hstate)
  have he₂ : Measurable e₂ := (measurable_restrictInner o R).comp (measurable_fst.comp hstate)
  obtain ⟨f, hF⟩ := hFill (fineSide Tb.side s n') o R δ
  let F : Set (OuterField o R) :=
    {u | ∃ w, ∀ p ∈ plaquettesIn S, curvature (glueField u w) p.1 p.2.1 p.2.2 ≤ δ}
  obtain ⟨hFm, hfm, hfc⟩ : MeasurableSet F ∧ Measurable (fun u : F => f u) ∧
      ∀ u ∈ F, ∀ p ∈ plaquettesIn S, curvature (glueField u (f u)) p.1 p.2.1 p.2.2 ≤ δ := hF
  classical
  let f' : OuterField o R → InnerField o R := fun u => if u ∈ F then f u else fun _ => 1
  have hf' : Measurable f' := measurable_ite_mem_of_restrict hFm hfm _
  let fill : OuterField o R → TorusField (fineSide Tb.side s n') := fun u => glueField u (f' u)
  have hfill : Measurable fill :=
    Measurable.comp (g := fun p : OuterField o R × InnerField o R => (glueField p.1 p.2 : TorusField _))
      (measurable_glueField o R) (measurable_id.prodMk hf')
  obtain ⟨gA, AA, hax'⟩ := hax x R (fineSide Tb.side s n') o hxa hR h16
  let cold : Set (TorusField (fineSide Tb.side s n')) :=
    {V | ∀ p ∈ plaquettesIn S, curvature V p.1 p.2.1 p.2.2 ≤ δ}
  obtain ⟨hgAm, hAAm, hgA⟩ : Measurable (fun V : cold => gA V) ∧ Measurable (fun V : cold => AA V) ∧
      ∀ V ∈ cold, gA V o = 1 ∧ (∀ b ∈ bondsWithin S, gaugeTransform (gA V) V b.1 b.2 = expUnit (AA V b)) ∧
        IsAxialSmall o R δ (AA V) := hax'
  have hcoldm : MeasurableSet cold := by
    have : IsClosed cold := by
      have e : cold = ⋂ p ∈ plaquettesIn S, {V | curvature V p.1 p.2.1 p.2.2 ≤ δ} := by
        ext V
        simp only [cold, Set.mem_setOf_eq, Set.mem_iInter]
      rw [e]
      exact isClosed_biInter fun p _ => isClosed_le (continuous_plaquetteCurvature _ _ _) continuous_const
    exact this.measurableSet
  let gE : TorusField (fineSide Tb.side s n') → TorusSite (fineSide Tb.side s n') → UnitQuaternion :=
    fun V => if V ∈ cold then gA V else fun _ => 1
  let AE : TorusField (fineSide Tb.side s n') → TorusBond (fineSide Tb.side s n') → imaginaryQuaternions :=
    fun V => if V ∈ cold then AA V else 0
  have hgE : Measurable gE := measurable_ite_mem_of_restrict hcoldm hgAm _
  have hAE : Measurable AE := measurable_ite_mem_of_restrict hcoldm hAAm _
  let gq : OuterData T k o R → TorusSite (fineSide Tb.side s n') → UnitQuaternion := fun q => gE (fill q.1)
  let Aq : OuterData T k o R → TorusBond (fineSide Tb.side s n') → imaginaryQuaternions := fun q => AE (fill q.1)
  have hgq : Measurable gq := hgE.comp (hfill.comp measurable_fst)
  have hAq : Measurable Aq := hAE.comp (hfill.comp measurable_fst)
  have hfillcold : ∀ u ∈ F, fill u ∈ cold := by
    intro u hu p hp
    have e : f' u = f u := if_pos hu
    show curvature (glueField u (f' u)) p.1 p.2.1 p.2.2 ≤ δ
    rw [e]
    exact hfc u hu p hp
  have hgqA : ∀ q : OuterData T k o R, q.1 ∈ F → gq q = gA (fill q.1) ∧ Aq q = AA (fill q.1) := fun q hq =>
    ⟨if_pos (hfillcold _ hq), if_pos (hfillcold _ hq)⟩
  obtain ⟨H, hHm, hHY, hHmass, h1116⟩ := hou' T β k s n' o x R (hdatum hxo) hx hR hsR
  let G₀ : Set (OuterData T k o R) := H ∩ (Prod.fst ⁻¹' F)
  have hG₀ : MeasurableSet G₀ := hHm.inter (measurable_fst hFm)
  obtain ⟨Bf, hBfm, hBf⟩ := hbk x R k (fineSide Tb.side s n') o hxb hR h16
  let Mq : OuterData T k o R → TorusPlaquette (fineSide Tb.side s n') → imaginaryQuaternions :=
    fun q => restrictedCurl S (Bf (Aq q))
  have hMq : Measurable Mq := (measurable_restrictedCurl_of_finset S).comp (hBfm.comp hAq)
  have haxG : ∀ q ∈ G₀, IsAxialSmall o R δ (Aq q) := fun q hq => by
    rw [(hgqA q hq.2).2]
    exact (hgA _ (hfillcold _ hq.2)).2.2
  have hYG : ∀ q ∈ G₀, Disjoint q.2.1 (supBall o (3 * R)) := fun q hq => hHY q hq.1
  obtain ⟨c, hcg, hcA, hcM, hcsub, hcorb, hcB, hcI, hcL, hcell, hcco, hcP, hcK, hnull⟩ :=
    hfr'' T β k (fineSide Tb.side s n') o x R G₀ gq Aq Mq (hdatum hxf) hx hR h16 hbs hG₀ hgq hAq hMq haxG hYG
  let D : MarkedSample (Tb.stepParameters y) (k + s) n' →
      MarkedSample (Tb.stepParameters y) k (fineSide Tb.side s n') :=
    sampleBelow (Tb.stepParameters y) k s n'
  have hDae : AEMeasurable D (markedSampleLaw T β (k + s) n') := by
    by_contra h
    have h0 : markedSampleLaw T β k (fineSide (Tb.stepParameters y).side s n') = 0 := by
      rw [← hmap]
      exact Measure.map_of_not_aemeasurable h
    have hne : markedSampleLaw T β k (fineSide Tb.side s n') ≠ 0 := IsProbabilityMeasure.ne_zero _
    exact hne h0
  have hreal : ∀ V : Set (MarkedSample (Tb.stepParameters y) k (fineSide Tb.side s n')), MeasurableSet V →
      (markedSampleLaw T β (k + s) n').real (D ⁻¹' V) = (markedSampleLaw T β k (fineSide Tb.side s n')).real V := by
    intro V hV
    have h3 : markedSampleLaw T β k (fineSide Tb.side s n') V = markedSampleLaw T β (k + s) n' (D ⁻¹' V) := by
      have h4 : markedSampleLaw T β k (fineSide Tb.side s n') = (markedSampleLaw T β (k + s) n').map D := hmap.symm
      rw [h4]
      exact Measure.map_apply_of_aemeasurable hDae hV
    simp only [Measure.real, h3]
  have hinX : ∀ u : MarkedSample (Tb.stepParameters y) k (fineSide Tb.side s n'), e₁ u ∈ G₀ →
      (∀ p ∈ plaquettesIn S, curvature (stageState T k _ u).1 p.1 p.2.1 p.2.2 ≤ δ) →
      e₂ u ∈ gaugeOrbitsOverEllipsoid Tb.coupling Tb.side k o R c₀ (gq (e₁ u)) (Aq (e₁ u)) (e₁ u).1 := by
    intro u hq hcoldu
    set W := (stageState T k _ u).1 with hW
    have hq1 : (e₁ u).1 ∈ F := hq.2
    obtain ⟨eg, eA⟩ := hgqA (e₁ u) hq1
    obtain ⟨-, hVg, hVa⟩ := hgA _ (hfillcold _ hq1)
    set V := fill (e₁ u).1 with hV
    have hoffV : ∀ b : TorusBond (fineSide Tb.side s n'), b ∉ bondsTouching o R → V b.1 b.2 = W b.1 b.2 := by
      intro b hb
      show glueField (restrictOuter o R W) _ b.1 b.2 = W b.1 b.2
      simp only [glueField]
      rw [dif_neg hb]
      rfl
    have hW' : ∀ p ∈ plaquettesIn S, curvature (gaugeTransform (gA V) W) p.1 p.2.1 p.2.2 ≤ δ := fun p hp => by
      rw [curvature_gaugeTransform]
      exact hcoldu p hp
    obtain ⟨γ, ζ, hγ, hζ, hc⟩ := hcf x R k (fineSide Tb.side s n') o (AA V) hxcf hR h16 hVa
      (gaugeTransform (gA V) W) hW'
      (fun b hb hbi => by
        rw [← hVg b hb]
        simp only [TorusFields.gaugeTransform]
        rw [hoffV b hbi])
    have hjoin : glueField (e₁ u).1 (e₂ u) = W := glueField_restrictOuter_restrictInner (o := o) (R := R) W
    refine ⟨(gA V)⁻¹ * γ * gA V, ζ, ?_, ?_, ?_⟩
    · intro z hz
      simp [hγ z hz]
    · rw [eA]
      refine ⟨hζ.1, le_trans hζ.2 ?_⟩
      have h5 : C₀c ≤ C₀ := le_trans (le_max_right _ _) (le_max_left _ _)
      have h6 : 0 ≤ (R : ℝ) ^ 4 * δ ^ 2 := by positivity
      calc C₀c * (R : ℝ) ^ 4 * δ ^ 2 = C₀c * ((R : ℝ) ^ 4 * δ ^ 2) := by ring
        _ ≤ C₀ * ((R : ℝ) ^ 4 * δ ^ 2) := mul_le_mul_of_nonneg_right h5 h6
        _ = c₀ := by simp only [hc₀]; ring
    · rw [eA, eg, hjoin]
      have e5 : gA V * ((gA V)⁻¹ * γ * gA V) = γ * gA V := by
        rw [mul_assoc, mul_inv_cancel_left]
      rw [e5, ← gaugeTransform_gaugeTransform]
      exact hc
  have hoffF : ∀ u : MarkedSample (Tb.stepParameters y) k (fineSide Tb.side s n'),
      (∀ p ∈ plaquettesIn S, curvature (stageState T k _ u).1 p.1 p.2.1 p.2.2 ≤ δ) → (e₁ u).1 ∈ F := by
    intro u hcoldu
    refine ⟨e₂ u, fun p hp => ?_⟩
    have hjoin : glueField (e₁ u).1 (e₂ u) = (stageState T k _ u).1 :=
      glueField_restrictOuter_restrictInner (o := o) (R := R) (stageState T k _ u).1
    rw [hjoin]
    exact hcoldu p hp
  have hB₁ : markedSampleLaw T β k (fineSide Tb.side s n') (e₁ ⁻¹' (H \ (Prod.fst ⁻¹' F))) = 0 := by
    have hm₁ : MeasurableSet (H \ (Prod.fst ⁻¹' F) : Set (OuterData T k o R)) := hHm.diff (measurable_fst hFm)
    have h3 := h1116 _ hm₁ Set.diff_subset
    have hz : ∀ A : Set (MarkedSample (Tb.stepParameters y) (k + s) n'), A = ∅ →
        (markedSampleLaw T β (k + s) n').real A = 0 :=
      fun A h => by
        rw [h]
        simp
    have h3b := h3.trans_eq (hz _ (Set.eq_empty_of_forall_notMem fun u hu => hu.1.2 (hoffF _ hu.2.1.2)))
    have h5 : (markedSampleLaw T β (k + s) n').real {u | outerDataOfSample T k s n' o R u ∈ H \ (Prod.fst ⁻¹' F)} =
        (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' (H \ (Prod.fst ⁻¹' F))) :=
      hreal _ (he₁ hm₁)
    have h8 : 11 / 16 * (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' (H \ (Prod.fst ⁻¹' F))) ≤ 0 := by
      rw [← h5]
      exact h3b
    have h6 : (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' (H \ (Prod.fst ⁻¹' F))) = 0 :=
      le_antisymm (by linarith) measureReal_nonneg
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h6
  set N : ℝ := (Tb.side : ℝ) ^ s with hN
  have hNpos : 0 < N := by positivity
  have hN1 : 1 ≤ N := one_le_pow₀ (by linarith)
  have hNR : 2 ^ 8 * N ≤ R := by
    have hL3 : ((2 ^ 8 * (Tb.side : ℝ))) ^ 3 ≤ R := by
      have : ((2 ^ 8 * Tb.side) ^ 3 : ℕ) ≤ R := by omega
      exact_mod_cast this
    have hcbrt : ∀ a : ℝ, 0 ≤ a → a = (a ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := fun a ha => by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
      norm_num
    have hcube : 2 ^ 8 * (Tb.side : ℝ) ≤ (R : ℝ) ^ (1 / 3 : ℝ) := by
      calc 2 ^ 8 * (Tb.side : ℝ) = ((2 ^ 8 * (Tb.side : ℝ)) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := hcbrt _ (by positivity)
        _ ≤ (R : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hL3 (by norm_num)
    have hsplit : (R : ℝ) = (R : ℝ) ^ (2 / 3 : ℝ) * (R : ℝ) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_add (by linarith)]
      norm_num
    have hNle : N ≤ (Tb.side : ℝ) * (R : ℝ) ^ (2 / 3 : ℝ) := by
      have e : N = (Tb.side : ℝ) * (Tb.side : ℝ) ^ (s - 1) := by
        rw [hN, ← pow_succ']
        congr 1
        omega
      rw [e]
      exact mul_le_mul_of_nonneg_left hsm.le (by linarith)
    have h23 : 0 ≤ (R : ℝ) ^ (2 / 3 : ℝ) := by positivity
    calc 2 ^ 8 * N ≤ 2 ^ 8 * ((Tb.side : ℝ) * (R : ℝ) ^ (2 / 3 : ℝ)) := by linarith
      _ = (R : ℝ) ^ (2 / 3 : ℝ) * (2 ^ 8 * (Tb.side : ℝ)) := by ring
      _ ≤ (R : ℝ) ^ (2 / 3 : ℝ) * (R : ℝ) ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_left hcube h23
      _ = R := hsplit.symm
  set O : TorusSite n' := siteAbove Tb.side s n' o with hO
  let near : TorusPlaquette n' → Prop := fun P => P ∈ plaquettesIn (Finset.univ : Finset (TorusSite n')) ∧
    N * supDist P.1 O ≤ (R : ℝ) / 8 + 2 * N
  let sumF : TorusPlaquette n' → (TorusBond (fineSide Tb.side s n') → imaginaryQuaternions) → imaginaryQuaternions :=
    fun P v => ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide Tb.side s n'))),
      blockWeight Tb.side s P p • lieFormCurl v p
  have hsumF : ∀ P, Continuous (sumF P) := fun P =>
    continuous_finset_sum _ fun p _ =>
      (continuous_const_smul (blockWeight Tb.side s P p)).comp (continuous_lieFormCurl p)
  let EP : TorusPlaquette n' →
      Set (OuterData T k o R × (TorusBond (fineSide Tb.side s n') → imaginaryQuaternions)) := fun P =>
    {z | ‖sumF P (Aq z.1 + z.2)‖ ≤ 12 * N * δ}
  have hEP : ∀ P, MeasurableSet (EP P) := fun P => by
    have h3 : Measurable fun z : OuterData T k o R × (TorusBond (fineSide Tb.side s n') → imaginaryQuaternions) =>
        ‖sumF P (Aq z.1 + z.2)‖ :=
      (hsumF P).norm.measurable.comp ((hAq.comp measurable_fst).add measurable_snd)
    exact measurableSet_le h3 measurable_const
  have hsup : ∀ P, near P → ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide Tb.side s n'))),
      blockWeight Tb.side s P p ≠ 0 → p ∈ plaquettesIn S := by
    intro P hP p hp hw
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    refine ⟨hp.1, fun z hz => ?_⟩
    have h3 := (hWts Tb.side (by omega) s n' P o).2 p hw z hz
    simp only [hS, supBall, Finset.mem_filter, Finset.mem_univ, true_and]
    have h4 : (supDist z o : ℝ) ≤ N * supDist P.1 O + 4 * N := by
      have : ((supDist z o : ℕ) : ℝ) ≤
          ((Tb.side ^ s * supDist P.1 (siteAbove Tb.side s n' o) + 4 * Tb.side ^ s : ℕ) : ℝ) := by
        exact_mod_cast h3
      push_cast at this
      exact this
    have h5 := hP.2
    linarith
  have hsum : ∀ P, near P → ∀ Fn : TorusPlaquette (fineSide Tb.side s n') → imaginaryQuaternions,
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide Tb.side s n'))), blockWeight Tb.side s P p • Fn p =
        ∑ p ∈ plaquettesIn S, blockWeight Tb.side s P p • Fn p := by
    intro P hP Fn
    symm
    refine Finset.sum_subset ?_ fun p hp hpS => ?_
    · intro p hp
      simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and, hS] at hp ⊢
      exact ⟨hp.1, fun z _ => trivial⟩
    · by_cases hw : blockWeight Tb.side s P p = 0
      · rw [hw, zero_smul]
      · exact absurd (hsup P hP p hp hw) hpS
  have hbadset : ∀ P : TorusPlaquette n', ∃ B : Set (OuterData T k o R), MeasurableSet B ∧ B ⊆ c.goodOuter ∧
      markedSampleLaw T β k (fineSide Tb.side s n') (e₁ ⁻¹' B) = 0 ∧
      ∀ q ∈ c.goodOuter, q ∉ B → near P → ENNReal.ofReal 0.65 ≤ c.coordLaw x c₀ q (Prod.mk q ⁻¹' EP P) := by
    intro P
    by_cases hnear : near P
    swap
    · exact ⟨∅, MeasurableSet.empty, Set.empty_subset _, by simp, fun q _ _ h => absurd h hnear⟩
    let B : Set (OuterData T k o R) := Subtype.val ''
      {q : c.goodOuter | c.coordLaw x c₀ q (Prod.mk q.1 ⁻¹' EP P) < ENNReal.ofReal 0.65}
    have hBm : MeasurableSet B :=
      MeasurableSet.subtype_image hcB.measurableSet_goodOuter (measurableSet_lt (hcK _ (hEP P)) measurable_const)
    have hBsub : B ⊆ c.goodOuter := by
      rintro q ⟨q', -, rfl⟩
      exact q'.2
    refine ⟨B, hBm, hBsub, ?_, fun q hq hqB _ => ?_⟩
    swap
    · by_contra hlt
      exact hqB ⟨⟨q, hq⟩, not_le.1 hlt, rfl⟩
    have hi := h1116 B hBm (fun q hq => (hcsub (hBsub hq)).1)
    have hL1 : (markedSampleLaw T β (k + s) n').real {u | outerDataOfSample T k s n' o R u ∈ B} =
        (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' B) := hreal _ (he₁ hBm)
    let a : MarkedSample (Tb.stepParameters y) k (fineSide Tb.side s n') →
        OuterData T k o R × (TorusBond (fineSide Tb.side s n') → imaginaryQuaternions) :=
      fun v => (e₁ v, c.coord (e₁ v) (e₂ v))
    have ha : Measurable a := he₁.prodMk (hcco.comp (he₁.prodMk he₂))
    let Bc : Set (OuterData T k o R × (TorusBond (fineSide Tb.side s n') → imaginaryQuaternions)) :=
      (Prod.fst ⁻¹' B) ∩ EP P
    have hBc : MeasurableSet Bc := (measurable_fst hBm).inter (hEP P)
    have hevm : MeasurableSet c.event := (he₁.prodMk he₂) hcB.measurableSet_orbitSet
    let Ev : Set (MarkedSample (Tb.stepParameters y) k (fineSide Tb.side s n')) := c.event ∩ a ⁻¹' Bc
    have hEvm : MeasurableSet Ev := hevm.inter (ha hBc)
    have hincl : ∀ A : Set (MarkedSample (Tb.stepParameters y) (k + s) n'),
        (∀ u ∈ A, HasBaseChoices (Tb.stepParameters y) k s n' u → D u ∈ Ev) →
        (markedSampleLaw T β (k + s) n').real A ≤ (markedSampleLaw T β k (fineSide Tb.side s n')).real Ev := by
      intro A hA
      rw [← hreal Ev hEvm]
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
      filter_upwards [hBases (Tb.stepParameters y) T β k s n'] with u hu hmem
      exact hA u hmem hu
    have hi2 := hi.trans (hincl _ (fun u hu hbase => by
      obtain ⟨hb, hcold, hgood⟩ := hu
      have hbq : e₁ (D u) ∈ B := hb
      have hq : e₁ (D u) ∈ c.goodOuter := hBsub hbq
      have hq0 : e₁ (D u) ∈ G₀ := hcsub hq
      have hX := hinX (D u) hq0 hcold.2
      have horb : (e₁ (D u), e₂ (D u)) ∈ c.orbitSet := (hcorb _).2 ⟨hq, hX⟩
      obtain ⟨γ, hγ, hζ, hon⟩ := hcI.mem_chart _ horb
      have hζ' : c.coord (e₁ (D u)) (e₂ (D u)) ∈
          sliceEllipsoid Tb.coupling Tb.side k o R (Aq (e₁ (D u))) c₀ := by
        have h3 := hζ
        rw [hcA] at h3
        exact h3
      have hjoin : glueField (e₁ (D u)).1 (e₂ (D u)) = topField (Tb.stepParameters y) k _ (D u) := by
        rw [← stageState_fst_eq_topField T k _ (D u)]
        exact glueField_restrictOuter_restrictInner (o := o) (R := R) _
      have hon' : IsInChart S (Aq (e₁ (D u))) (c.coord (e₁ (D u)) (e₂ (D u)))
          (gaugeTransform (gq (e₁ (D u)) * γ) (topField (Tb.stepParameters y) k _ (D u))) := by
        have h3 := hon
        rw [hcA, hcg] at h3
        have h4 : glueField (e₁ (D u), e₂ (D u)).1.1 (e₁ (D u), e₂ (D u)).2 =
            topField (Tb.stepParameters y) k _ (D u) := hjoin
        rw [h4] at h3
        exact h3
      have hcold' : ∀ p ∈ plaquettesIn S,
          curvature (topField (Tb.stepParameters y) k _ (D u)) p.1 p.2.1 p.2.2 ≤ δ := by
        rw [← stageState_fst_eq_topField T k _ (D u)]
        exact hcold.2
      have hcirc := hci' T β k s n' o x R (Aq (e₁ (D u))) (c.coord (e₁ (D u)) (e₂ (D u)))
        (gq (e₁ (D u)) * γ) u (hdatum hxi) hx hR hsR (haxG _ hq0) hζ' hon' hcold' hgood hbase P hnear.1 hnear.2
      exact ⟨horb, hbq, hcirc⟩))
    have hl := hcL.integral_eq (Bc.indicator 1) (measurable_one.indicator hBc) ⟨1, fun z => by
      by_cases hz : z ∈ Bc
      · simp [Set.indicator_of_mem hz]
      · simp [Set.indicator_of_notMem hz]⟩
    have hLHS : ∫ u in c.event, Bc.indicator
        (1 : OuterData T k o R × (TorusBond (fineSide Tb.side s n') → imaginaryQuaternions) → ℝ) (a u)
        ∂(markedSampleLaw T β k (fineSide Tb.side s n')) =
        (markedSampleLaw T β k (fineSide Tb.side s n')).real Ev := by
      have e : (fun u => Bc.indicator
          (1 : OuterData T k o R × (TorusBond (fineSide Tb.side s n') → imaginaryQuaternions) → ℝ) (a u)) =
          (a ⁻¹' Bc).indicator 1 := by
        funext u
        by_cases h : a u ∈ Bc
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show u ∈ a ⁻¹' Bc from h)]
          rfl
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show u ∉ a ⁻¹' Bc from h)]
      rw [e, setIntegral_indicator (ha hBc)]
      simp [Ev]
    let gfn : MarkedSample (Tb.stepParameters y) k (fineSide Tb.side s n') → ℝ :=
      (e₁ ⁻¹' B).indicator fun _ => (0.65 : ℝ)
    have hg : Integrable gfn (markedSampleLaw T β k (fineSide Tb.side s n')) :=
      (integrable_const (0.65 : ℝ)).indicator (he₁ hBm)
    have hg0 : ∀ u, 0 ≤ gfn u := fun u => Set.indicator_nonneg (fun _ _ => by norm_num) u
    have hinner : ∀ u ∈ c.event, ∫ ζ, Bc.indicator
        (1 : OuterData T k o R × (TorusBond (fineSide Tb.side s n') → imaginaryQuaternions) → ℝ) (e₁ u, ζ)
        ∂(c.coordLaw x c₀ (e₁ u)) ≤ gfn u := by
      intro u hu
      have hq : e₁ u ∈ c.goodOuter := hcB.fst_mem_goodOuter _ hu
      haveI := hcP _ hq
      by_cases hqB : e₁ u ∈ B
      · have hgu : gfn u = 0.65 := Set.indicator_of_mem (show u ∈ e₁ ⁻¹' B from hqB) _
        obtain ⟨q', hlt, hq'e⟩ := hqB
        have e : (fun ζ => Bc.indicator
            (1 : OuterData T k o R × (TorusBond (fineSide Tb.side s n') → imaginaryQuaternions) → ℝ) (e₁ u, ζ)) =
            (Prod.mk (e₁ u) ⁻¹' EP P).indicator 1 := by
          funext ζ
          by_cases h : (e₁ u, ζ) ∈ EP P
          · have h3 : (e₁ u, ζ) ∈ Bc := ⟨⟨q', hlt, hq'e⟩, h⟩
            rw [Set.indicator_of_mem h3, Set.indicator_of_mem (show ζ ∈ Prod.mk (e₁ u) ⁻¹' EP P from h)]
            rfl
          · have h3 : (e₁ u, ζ) ∉ Bc := fun h4 => h h4.2
            rw [Set.indicator_of_notMem h3, Set.indicator_of_notMem (show ζ ∉ Prod.mk (e₁ u) ⁻¹' EP P from h)]
        rw [e, integral_indicator_one (measurable_prodMk_left (hEP P)), hgu]
        have hlt' : c.coordLaw x c₀ (e₁ u) (Prod.mk (e₁ u) ⁻¹' EP P) < ENNReal.ofReal 0.65 := by
          have h3 : c.coordLaw x c₀ q' (Prod.mk q'.1 ⁻¹' EP P) < ENNReal.ofReal 0.65 := hlt
          rw [hq'e] at h3
          exact h3
        exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hlt'.le
      · have hgu : gfn u = 0 := Set.indicator_of_notMem (show u ∉ e₁ ⁻¹' B from hqB) _
        have e : ∀ ζ, Bc.indicator
            (1 : OuterData T k o R × (TorusBond (fineSide Tb.side s n') → imaginaryQuaternions) → ℝ) (e₁ u, ζ) = 0 :=
          fun ζ => Set.indicator_of_notMem (fun h => hqB h.1) _
        simp only [e, integral_zero, hgu, le_refl]
    have hRHS : ∫ u in c.event, ∫ ζ, Bc.indicator
        (1 : OuterData T k o R × (TorusBond (fineSide Tb.side s n') → imaginaryQuaternions) → ℝ) (e₁ u, ζ)
        ∂(c.coordLaw x c₀ (e₁ u)) ∂(markedSampleLaw T β k (fineSide Tb.side s n')) ≤
        0.65 * (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' B) := by
      calc _ ≤ ∫ u in c.event, gfn u ∂(markedSampleLaw T β k (fineSide Tb.side s n')) := by
            refine integral_mono_of_nonneg (ae_of_all _ fun u => ?_) hg.integrableOn ?_
            · refine integral_nonneg fun ζ => ?_
              exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
            · exact (ae_restrict_iff' hevm).2 (ae_of_all _ hinner)
        _ ≤ ∫ u, gfn u ∂(markedSampleLaw T β k (fineSide Tb.side s n')) :=
            setIntegral_le_integral hg (ae_of_all _ hg0)
        _ = 0.65 * (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' B) := by
            rw [integral_indicator (he₁ hBm), setIntegral_const, smul_eq_mul, mul_comm]
    have hfin : 11 / 16 * (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' B) ≤
        0.65 * (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' B) := by
      have h3 : 11 / 16 * (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' B) ≤
          (markedSampleLaw T β k (fineSide Tb.side s n')).real Ev := by
        rw [← hL1]
        exact hi2
      rw [← hLHS] at h3
      refine h3.trans (le_of_eq_of_le ?_ hRHS)
      exact hl
    have hz : (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' B) = 0 := by
      have h3 : 0 ≤ (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' B) := measureReal_nonneg
      norm_num at hfin
      linarith
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hz
  choose Bad hBadm hBadsub hBadnull hBadlaw using hbadset
  let good' : Set (OuterData T k o R) := c.goodOuter \ ⋃ P, Bad P
  have hgood' : MeasurableSet good' := hcB.measurableSet_goodOuter.diff (MeasurableSet.iUnion hBadm)
  have hsub' : good' ⊆ c.goodOuter := Set.diff_subset
  have hCb0 : Cb ≤ max Cb 0 := le_max_left _ _
  have hsizeq : ∀ q ∈ c.goodOuter, (∀ p ∈ plaquettesIn S, ‖lieFormCurl (Bf (Aq q)) p‖ ≤ Cs * (R : ℝ) ^ 2 * δ) ∧
      ∀ (l : List (Fin 4)), ∀ p ∈ plaquettesIn (supBall o ((R : ℝ) / 4)),
        ‖iteratedDiff l (Mq q) p‖ ≤ Cj l.length * ((R : ℝ) ^ l.length)⁻¹ * δ := by
    intro q hq
    obtain ⟨b1, b2, b3, b4, b5⟩ := hBf _ (haxG q (hcsub hq))
    refine hsz x R k (fineSide Tb.side s n') o (Bf (Aq q)) hxsz hR h16 (le_trans b3 ?_)
      (fun b hb => le_trans (b4 b hb) ?_) b2
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCb0 (by positivity)) (by positivity)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCb0 (by positivity)) hδ0
  have hR4 : (100 : ℝ) ≤ (R : ℝ) ^ 4 := by
    have h3 : 4 ≤ R := by
      have h4 : 4 ≤ (2 ^ 8 * Tb.side) ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
      omega
    have h5 : (4 : ℝ) ≤ R := by exact_mod_cast h3
    calc (100 : ℝ) ≤ 4 ^ 4 := by norm_num
      _ ≤ (R : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) h5 4
  set ε' : ℝ := max (Cf * (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) 0 with hε'
  have hε'0 : 0 ≤ ε' := le_max_right _ _
  have hε'1 : ε' ≤ 1 / 100 := by
    refine max_le ?_ (by norm_num)
    calc Cf * (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3
        = Cf * ((R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) := by ring
      _ ≤ 1 / 100 := hεs
  have hη : Real.exp (-((R : ℝ) ^ 4)) ≤ 1 / 101 := by
    rw [Real.exp_neg, one_div]
    refine inv_anti₀ (by norm_num) ?_
    have := Real.add_one_le_exp ((R : ℝ) ^ 4)
    linarith
  have hnum : (0.6 : ℝ) ≤ 0.65 * Real.exp (-(2 * ε')) * (1 - Real.exp (-((R : ℝ) ^ 4))) := by
    have h3 := Real.add_one_le_exp (-(2 * ε'))
    have h4 : (0.98 : ℝ) ≤ Real.exp (-(2 * ε')) := by linarith
    have h5 : (100 / 101 : ℝ) ≤ 1 - Real.exp (-((R : ℝ) ^ 4)) := by linarith
    calc (0.6 : ℝ) ≤ 0.65 * 0.98 * (100 / 101) := by norm_num
      _ ≤ 0.65 * Real.exp (-(2 * ε')) * (1 - Real.exp (-((R : ℝ) ^ 4))) := by gcongr
  have hblockq : ∀ q ∈ good', ∀ P ∈ plaquettesIn (Finset.univ : Finset (TorusSite n')),
      (Tb.side : ℝ) ^ s * supDist P.1 O ≤ (R : ℝ) / 8 + 2 * (Tb.side : ℝ) ^ s →
      ‖∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide Tb.side s n'))),
          blockWeight Tb.side s P p • Mq q p‖ ≤ 13 * (Tb.side : ℝ) ^ s * δ := by
    intro q hq P hPm hPd
    have hnear : near P := ⟨hPm, hPd⟩
    have hqc : q ∈ c.goodOuter := hq.1
    have hq0 := hcsub hqc
    have hqB : q ∉ Bad P := fun h => hq.2 (Set.mem_iUnion.2 ⟨P, h⟩)
    have hlaw := hBadlaw P q hqc hqB hnear
    obtain ⟨hgp, hgm⟩ := hcL.ellipsoid_mass q hqc
    rw [hcA] at hgp hgm
    haveI := hgp
    obtain ⟨b1, b2, b3, b4, b5⟩ := hBf _ (haxG q hq0)
    have hsec : MeasurableSet (Prod.mk q ⁻¹' EP P) := measurable_prodMk_left (hEP P)
    have hwm : Measurable fun ζ => c.weight q ζ :=
      hcB.measurable_weight.comp (measurable_const.prodMk measurable_id :
        Measurable fun ζ : TorusBond (fineSide Tb.side s n') → imaginaryQuaternions => ((⟨q, hqc⟩ : c.goodOuter), ζ))
    have hlaw' : ENNReal.ofReal 0.65 ≤ normalize (((sliceGaussian Tb.coupling Tb.side k o R x (Aq q)).restrict
        (sliceEllipsoid Tb.coupling Tb.side k o R (Aq q) c₀)).withDensity fun ζ => ENNReal.ofReal (c.weight q ζ))
        (Prod.mk q ⁻¹' EP P) := by
      have h3 := hlaw
      unfold BoxChart.coordLaw at h3
      rw [hcA] at h3
      exact h3
    have h06 := gaussianMass_ge_of_weightedLaw (hcell q) hsec hwm hε'0 (fun ζ hζ => by
      have h3 := hcL.weight_bounds q hqc ζ (by rw [hcA]; exact hζ)
      exact ⟨h3.1, le_trans h3.2 (le_max_left _ _)⟩) hgm (lt_of_le_of_lt hη (by norm_num)) hnum hlaw'
    have hw2 : ∑ p ∈ plaquettesIn S, blockWeight Tb.side s P p ^ 2 ≤ 1 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => by positivity)
        (hWts Tb.side (by omega) s n' P o).1
      intro p hp
      simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and, hS] at hp ⊢
      exact ⟨hp.1, fun z _ => trivial⟩
    have hmean := hmn x R k (fineSide Tb.side s n') o (Aq q) (Bf (Aq q)) hxm hR h16 (haxG q hq0) b1 b2
      (Prod.mk q ⁻¹' EP P ∩ sliceEllipsoid Tb.coupling Tb.side k o R (Aq q) c₀) (blockWeight Tb.side s P)
      (12 * N * δ) (hsec.inter (hcell q)) hw2 h06 (fun ζ hζ => by
        rw [← hsum P hnear]
        exact hζ.1)
    rw [hsum P hnear]
    have heq : ∑ p ∈ plaquettesIn S, blockWeight Tb.side s P p • Mq q p =
        ∑ p ∈ plaquettesIn S, blockWeight Tb.side s P p • lieFormCurl (Bf (Aq q)) p := by
      refine Finset.sum_congr rfl fun p hp => ?_
      simp only [Mq, restrictedCurl, if_pos hp]
    rw [heq]
    refine le_trans hmean ?_
    have hsmall : Km * x ^ (-(1 / 2 : ℝ)) ≤ N * δ := by
      have hxp : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
      have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
      have hK1 : Km ≤ Real.log x := by
        have := le_abs_self Km
        linarith
      calc Km * x ^ (-(1 / 2 : ℝ)) ≤ Real.log x * x ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hK1 hxp
        _ ≤ δ := by
            simp only [hδ, boxScale]
            nlinarith [mul_nonneg hlog hxp]
        _ ≤ N * δ := by nlinarith
    have e13 : 12 * N * δ + N * δ = 13 * N * δ := by ring
    linarith
  have hflat : ∀ q ∈ good', ∀ p ∈ plaquettesIn (supBall o ((R : ℝ) / 8)),
      ‖Mq q p‖ ≤ Cbl * (R : ℝ) ^ (-(2 / 3 : ℝ)) * δ := by
    intro q hq
    exact hblk s n' R o δ (Mq q) hRbl rfl h16 hδ0 (fun l hl p hp => by
      have h3 := (hsizeq q hq.1).2 l p hp
      rw [hl] at h3
      exact h3) (hblockq q hq)
  have hCf : Cf ≤ Cc := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hCs : Cs ≤ Cc := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hCbl : Cbl ≤ Cc := le_trans (le_max_right _ _) (le_max_left _ _)
  have ht9 : 0 ≤ (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3 := by
    have : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h3 : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
    positivity
  have hLaw' := restrictChart_hasLaw hcL hgood' hsub' he₁
  refine ⟨restrictChart c good', restrictChart_isMeasurable hcB hgood' hsub', ?_,
    fun p hp => hHY p.1 (hcsub (hsub' hp.2)).1,
    isInGauge_mono ?_ hδ0 (restrictChart_isInGauge hcI good'),
    ⟨hLaw'.integral_eq, fun q hq ζ hζ => ?_, hLaw'.ellipsoid_mass⟩, ⟨?_, ?_, ?_, ?_⟩,
    fun u => (hker k (fineSide Tb.side s n') o R hRk h16).2.2 u⟩
  · intro p hp
    have hm1 := hHmass (p + 1) (le_trans (le_max_left _ _) hp)
    have hm1' : 1 - x ^ (-((p + 1 : ℕ) : ℝ)) ≤ (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' H) := by
      rw [← hreal _ (he₁ hHm)]
      exact hm1
    obtain ⟨hc1, -⟩ := hco' T β k s n' o x R (hdatum hxc) hx hR hsR (p + 1) (le_trans (le_max_right _ _) hp)
    let Cd : Set (MarkedSample (Tb.stepParameters y) k (fineSide Tb.side s n')) :=
      {u | ¬ IsColdOnBox o R δ (stageState T k _ u).1 (stageState T k _ u).2.1}
    have hc1' : (markedSampleLaw T β k (fineSide Tb.side s n')).real Cd ≤ x ^ (-((p + 1 : ℕ) : ℝ)) := hc1
    let Nn : Set (MarkedSample (Tb.stepParameters y) k (fineSide Tb.side s n')) :=
      {u | e₁ u ∈ G₀ \ c.goodOuter ∧
        e₂ u ∈ gaugeOrbitsOverEllipsoid Tb.coupling Tb.side k o R c₀ (gq (e₁ u)) (Aq (e₁ u)) (e₁ u).1}
    have hNn : markedSampleLaw T β k (fineSide Tb.side s n') Nn = 0 := hnull
    let Z : Set (MarkedSample (Tb.stepParameters y) k (fineSide Tb.side s n')) :=
      e₁ ⁻¹' (H \ (Prod.fst ⁻¹' F)) ∪ Nn ∪ ⋃ P, e₁ ⁻¹' Bad P
    have hZ : markedSampleLaw T β k (fineSide Tb.side s n') Z = 0 := by
      refine measure_union_null (measure_union_null hB₁ hNn) ?_
      exact measure_iUnion_null fun P => hBadnull P
    have hevm : MeasurableSet (restrictChart c good').event :=
      (he₁.prodMk he₂) (hcB.measurableSet_orbitSet.inter (measurable_fst hgood'))
    have hsubset : (restrictChart c good').eventᶜ ⊆ (e₁ ⁻¹' H)ᶜ ∪ Cd ∪ Z := by
      intro u hu
      by_contra hcon
      simp only [Set.mem_union, not_or] at hcon
      obtain ⟨⟨hH, hC⟩, hZu⟩ := hcon
      have hH' : e₁ u ∈ H := by
        by_contra h
        exact hH h
      have hC' : IsColdOnBox o R δ (stageState T k _ u).1 (stageState T k _ u).2.1 := by
        by_contra h
        exact hC h
      have hZ1 : e₁ u ∉ H \ (Prod.fst ⁻¹' F) := fun h => hZu (Or.inl (Or.inl h))
      have hZ2 : u ∉ Nn := fun h => hZu (Or.inl (Or.inr h))
      have hZ3 : ∀ P, e₁ u ∉ Bad P := fun P h => hZu (Or.inr (Set.mem_iUnion.2 ⟨P, h⟩))
      have hG : e₁ u ∈ G₀ := ⟨hH', by
        by_contra h
        exact hZ1 ⟨hH', h⟩⟩
      have hX := hinX u hG hC'.2
      have hgd : e₁ u ∈ c.goodOuter := by
        by_contra h
        exact hZ2 ⟨⟨hG, h⟩, hX⟩
      have hgd' : e₁ u ∈ good' := ⟨hgd, fun h => by
        obtain ⟨P, hP⟩ := Set.mem_iUnion.1 h
        exact hZ3 P hP⟩
      exact hu ⟨(hcorb _).2 ⟨hgd, hX⟩, hgd'⟩
    have hx2 : x ^ (-((p + 1 : ℕ) : ℝ)) ≤ x ^ (-(p : ℝ)) / 2 := by
      have e1 : x ^ (-((p + 1 : ℕ) : ℝ)) = x ^ (-(p : ℝ)) * x⁻¹ := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hx0]
        congr 1
        push_cast
        ring
      rw [e1, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx0.le _)
      exact inv_anti₀ (by norm_num) (by linarith)
    have hcompl : (markedSampleLaw T β k (fineSide Tb.side s n')).real (restrictChart c good').event =
        1 - (markedSampleLaw T β k (fineSide Tb.side s n')).real (restrictChart c good').eventᶜ := by
      rw [measureReal_compl hevm]
      simp
    have hHc : (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' H)ᶜ =
        1 - (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' H) := by
      rw [measureReal_compl (he₁ hHm)]
      simp
    have hZr : (markedSampleLaw T β k (fineSide Tb.side s n')).real Z = 0 := by
      simp [Measure.real, hZ]
    have hU : (markedSampleLaw T β k (fineSide Tb.side s n')).real (restrictChart c good').eventᶜ ≤
        (markedSampleLaw T β k (fineSide Tb.side s n')).real (e₁ ⁻¹' H)ᶜ +
          (markedSampleLaw T β k (fineSide Tb.side s n')).real Cd +
          (markedSampleLaw T β k (fineSide Tb.side s n')).real Z := by
      refine le_trans (measureReal_mono hsubset (measure_ne_top _ _)) ?_
      refine le_trans (measureReal_union_le _ _) ?_
      have := measureReal_union_le (μ := markedSampleLaw T β k (fineSide Tb.side s n')) (e₁ ⁻¹' H)ᶜ Cd
      linarith
    rw [hcompl]
    linarith
  · exact le_trans hCf (le_refl _)
  · obtain ⟨w1, w2⟩ := hcL.weight_bounds q (hsub' hq) ζ hζ
    refine ⟨w1, le_trans w2 ?_⟩
    calc Cf * (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3
        = Cf * ((R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) := by ring
      _ ≤ Cc * ((R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) := mul_le_mul_of_nonneg_right hCf ht9
      _ = _ := by ring
  · intro q hq u
    have hq0 := hcsub (hsub' hq)
    have h3 := (hBf _ (haxG q hq0)).2.2.2.2 u
    have e1 : (fun ζ => colourPairing (supBall o (2 * R)) u fun p =>
          lieFormCurl ((restrictChart c good').background q + ζ) p - (restrictChart c good').meanCurl q p) =
        fun ζ => colourPairing S u fun p => lieFormCurl (Aq q + ζ) p - lieFormCurl (Bf (Aq q)) p := by
      funext ζ
      show colourPairing S u (fun p => lieFormCurl (c.background q + ζ) p - c.meanCurl q p) = _
      rw [hcA, hcM]
      unfold colourPairing
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun p hp => ?_
      simp only [Mq, restrictedCurl, if_pos hp]
    rw [e1, show (restrictChart c good').background q = Aq q by
      show c.background q = Aq q
      rw [hcA]]
    exact h3
  · intro q hq p hp
    have h3 := (hsizeq q (hsub' hq)).1 p hp
    have e1 : (restrictChart c good').meanCurl q p = lieFormCurl (Bf (Aq q)) p := by
      show c.meanCurl q p = _
      rw [hcM]
      have hp' : p ∈ plaquettesIn S := hp
      simp only [Mq, restrictedCurl, if_pos hp']
    rw [e1]
    refine le_trans h3 ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCs (by positivity)) hδ0
  · intro q hq l p hp
    have h3 := (hsizeq q (hsub' hq)).2 l p hp
    have e1 : (restrictChart c good').meanCurl = Mq := hcM
    rw [e1]
    exact h3
  · intro q hq p hp
    have h3 := hflat q hq p hp
    have e1 : (restrictChart c good').meanCurl = Mq := hcM
    rw [e1]
    refine le_trans h3 ?_
    have h4 : 0 ≤ (R : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbl h4) hδ0
end YangMills.Construction.BoxGaussian
end
