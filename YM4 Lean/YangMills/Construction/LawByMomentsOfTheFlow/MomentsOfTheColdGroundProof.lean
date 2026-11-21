import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelow
import YangMills.Construction.LawByMomentsOfTheFlow.FieldOfTheColdGround
import YangMills.Construction.LawByMomentsOfTheFlow.MeansOfTheColdCoordinates
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheColdGround
import YangMills.Construction.ResponseInTheExpansion.ColdLawOfAStepIsALaw
import YangMills.Construction.ResponseInTheExpansion.FarSpinsMoveAVariableProof
import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheColdLawAtGivenParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open BlockAverages ColdStepAtMirrorFrames StepSettings TorusFields TorusLumps RenormalizationStepParameters WeightedResponses
  Interpolation TopLevelSites
private theorem probability_and_lintegral_of_density {X : Type} [MeasurableSpace X] (μ : Measure X)
    (g : X → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgpos : 0 < ∫ x, g x ∂μ) :
    IsProbabilityMeasure (((∫⁻ x, ENNReal.ofReal (g x) ∂μ)⁻¹) • μ.withDensity fun x => ENNReal.ofReal (g x)) ∧
    ∀ f : X → ℝ, Measurable f → (∀ x, 0 ≤ f x) → Integrable (fun x => f x * g x) μ →
      ∫⁻ x, ENNReal.ofReal (f x) ∂(((∫⁻ x, ENNReal.ofReal (g x) ∂μ)⁻¹) • μ.withDensity fun x => ENNReal.ofReal (g x)) =
        ENNReal.ofReal ((∫ x, f x * g x ∂μ) / ∫ x, g x ∂μ) := by
  have hint : Integrable g μ := by
    by_contra h
    rw [integral_undef h] at hgpos
    exact lt_irrefl _ hgpos
  have hmass : ∫⁻ x, ENNReal.ofReal (g x) ∂μ = ENNReal.ofReal (∫ x, g x ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hg0)).symm
  have hne0 : ENNReal.ofReal (∫ x, g x ∂μ) ≠ 0 := (ENNReal.ofReal_pos.2 hgpos).ne'
  have hnetop : ENNReal.ofReal (∫ x, g x ∂μ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hgm : AEMeasurable (fun x => ENNReal.ofReal (g x)) μ := hint.1.aemeasurable.ennreal_ofReal
  refine ⟨⟨?_⟩, fun f hf hf0 hfi => ?_⟩
  · rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hmass, smul_eq_mul,
      ENNReal.inv_mul_cancel hne0 hnetop]
  · rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul₀ hgm hf.ennreal_ofReal.aemeasurable, hmass]
    have heq : ∫⁻ x, ((fun x => ENNReal.ofReal (g x)) * fun x => ENNReal.ofReal (f x)) x ∂μ =
        ENNReal.ofReal (∫ x, f x * g x ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ fun x => mul_nonneg (hf0 x) (hg0 x))]
      refine lintegral_congr fun x => ?_
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (hg0 x), mul_comm]
    rw [heq, smul_eq_mul, ← ENNReal.ofReal_inv_of_pos hgpos, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_eq_inv_mul]
private theorem ae_of_density_eq_zero {X : Type} [MeasurableSpace X] (μ : Measure X) (g : X → ℝ) (c : ENNReal)
    (P : X → Prop) (hmeas : MeasurableSet {x | ¬ P x}) (h : ∀ x, ¬ P x → g x = 0) :
    ∀ᵐ x ∂(c • μ.withDensity fun x => ENNReal.ofReal (g x)), P x := by
  rw [ae_iff, Measure.smul_apply, withDensity_apply _ hmeas]
  have : ∫⁻ x in {x | ¬ P x}, ENNReal.ofReal (g x) ∂μ = 0 := by
    rw [setLIntegral_congr_fun (g := fun _ => 0) hmeas (fun x hx => by simp [h x hx])]
    simp
  rw [this]
  simp
private theorem coordNorm_eq_norm (v : EuclideanSpace ℝ (Fin 3)) : coordNorm v = ‖v‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
variable {S : StepSetup} {n : ℕ} [NeZero n]
private theorem chartDensity_nonneg (s : ChartSetting S n) (η : FreeCoords s.free) : 0 ≤ chartDensity s η := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.chartDensity_nonneg <;> assumption
private theorem chartDensity_eq_zero_off_balls (s : ChartSetting S n) (η : FreeCoords s.free)
    (h : ¬ ∀ b, coordNorm (η b) < S.ballRadius) :
    chartDensity s η = 0 := by
  push Not at h
  obtain ⟨b, hb⟩ := h
  unfold chartDensity ChartSetting.cutoffProduct
  rw [Finset.prod_eq_zero (Finset.mem_univ b) (by unfold cutoffFactor; rw [if_neg (not_lt.2 hb)]), zero_mul]
private theorem ballLaw_of_moments {free : Finset (TorusBond (n * S.params.side))} (g : FreeCoords free → ℝ)
    (q : ℕ) (c : ℝ) (hg0 : ∀ η, 0 ≤ g η) (hoff : ∀ η, (¬ ∀ b, coordNorm (η b) < S.ballRadius) → g η = 0)
    (hgpos : 0 < ∫ η, g η) (hmom : ∀ b, weightedMean g (fun η => ‖η b‖ ^ (2 * q)) ≤ c) :
    IsProbabilityMeasure (((∫⁻ η, ENNReal.ofReal (g η))⁻¹) • (volume.withDensity fun η => ENNReal.ofReal (g η))) ∧
      (∀ᵐ η ∂(((∫⁻ η, ENNReal.ofReal (g η))⁻¹) • (volume.withDensity fun η => ENNReal.ofReal (g η))),
        ∀ b, coordNorm (η b) < S.ballRadius) ∧
      ∀ b, ∫⁻ η, ENNReal.ofReal (coordNorm (η b) ^ (2 * q))
        ∂(((∫⁻ η, ENNReal.ofReal (g η))⁻¹) • (volume.withDensity fun η => ENNReal.ofReal (g η))) ≤ ENNReal.ofReal c := by
  obtain ⟨hprob, hlin⟩ := probability_and_lintegral_of_density volume g hg0 hgpos
  refine ⟨hprob, ae_of_density_eq_zero volume _ _ _ ?_ hoff, fun b => ?_⟩
  · have : MeasurableSet {η : FreeCoords free | ∀ b, ‖η b‖ < S.ballRadius} := by
      have hset : {η : FreeCoords free | ∀ b, ‖η b‖ < S.ballRadius} = ⋂ b, {η | ‖η b‖ < S.ballRadius} := by
        ext η
        simp
      rw [hset]
      exact MeasurableSet.iInter fun b => measurableSet_lt (measurable_norm.comp (measurable_pi_apply b)) measurable_const
    have hcompl : {η : FreeCoords free | ¬ ∀ b, coordNorm (η b) < S.ballRadius} =
        {η | ∀ b, ‖η b‖ < S.ballRadius}ᶜ := by
      ext η
      simp [coordNorm_eq_norm]
    rw [hcompl]
    exact this.compl
  · have hint : Integrable (fun η => ‖η b‖ ^ (2 * q) * g η) := by
      have hgi : Integrable g := by
        by_contra h
        rw [integral_undef h] at hgpos
        exact lt_irrefl _ hgpos
      refine Integrable.mono' (hgi.const_mul (S.ballRadius ^ (2 * q)))
        ((((continuous_apply b).norm.pow _).aestronglyMeasurable).mul hgi.1) (ae_of_all _ fun η => ?_)
      by_cases hη : ∀ b, coordNorm (η b) < S.ballRadius
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 η), abs_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_right ?_ (hg0 η)
        have := hη b
        rw [coordNorm_eq_norm] at this
        exact pow_le_pow_left₀ (norm_nonneg _) this.le _
      · rw [hoff η hη]
        simp
    have hswap : ∫⁻ η, ENNReal.ofReal (coordNorm (η b) ^ (2 * q))
        ∂(((∫⁻ η, ENNReal.ofReal (g η))⁻¹) • (volume.withDensity fun η => ENNReal.ofReal (g η))) =
        ∫⁻ η, ENNReal.ofReal (‖η b‖ ^ (2 * q))
        ∂(((∫⁻ η, ENNReal.ofReal (g η))⁻¹) • (volume.withDensity fun η => ENNReal.ofReal (g η))) :=
      lintegral_congr fun η => by rw [coordNorm_eq_norm]
    rw [hswap]
    rw [hlin (fun η => ‖η b‖ ^ (2 * q)) (((continuous_apply b).norm.pow _).measurable) (fun η => by positivity) hint]
    exact ENNReal.ofReal_le_ofReal (hmom b)
private theorem moments_of_eq_fine_field (V : TorusField n) (q : ℕ) (c : ℝ) (s : ChartSetting S n)
    (hs : s = ({ coldChartSetting S V with fine := (coldChartSetting S V).field 0 } : ChartSetting S n))
    (hdens : ∀ η, chartDensity ({ coldChartSetting S V with fine := (coldChartSetting S V).field 0 } : ChartSetting S n) η =
      chartDensity (coldChartSetting S V) η)
    (hgpos : 0 < ∫ η, chartDensity (coldChartSetting S V) η)
    (hmom : ∀ b, weightedMean (chartDensity (coldChartSetting S V)) (fun η => ‖η b‖ ^ (2 * q)) ≤ c) :
    (0 < ∫ η, chartDensity s η) ∧ ∀ b, weightedMean (chartDensity s) (fun η => ‖η b‖ ^ (2 * q)) ≤ c := by
  subst hs
  constructor
  · have hint : (∫ η, chartDensity ({ coldChartSetting S V with fine := (coldChartSetting S V).field 0 } : ChartSetting S n) η) =
        ∫ η, chartDensity (coldChartSetting S V) η := integral_congr_ae (ae_of_all _ hdens)
    rw [hint]
    exact hgpos
  · intro b
    have hint : (∫ η, chartDensity ({ coldChartSetting S V with fine := (coldChartSetting S V).field 0 } : ChartSetting S n) η) =
        ∫ η, chartDensity (coldChartSetting S V) η := integral_congr_ae (ae_of_all _ hdens)
    have hint2 : (∫ η, ‖η b‖ ^ (2 * q) * chartDensity ({ coldChartSetting S V with fine := (coldChartSetting S V).field 0 } : ChartSetting S n) η) =
        ∫ η, ‖η b‖ ^ (2 * q) * chartDensity (coldChartSetting S V) η :=
      integral_congr_ae (ae_of_all _ fun η => by simp only [hdens])
    unfold weightedMean
    rw [hint, hint2]
    exact hmom b
theorem coldGroundMoments_proof (hMom : ResponseInTheExpansion.coldHalfLawMomentsStatement)
    (hMe : coldCoordinateMeansStatement) (hLaw : ResponseInTheExpansion.coldHalfLawIsLawStatement)
    (hF : coldGroundFieldStatement) (hRow : ColdExpansionRegular) :
    coldGroundMomentsStatement := by
  intro a ha
  obtain ⟨L₃, r₃, C₃, hr₃, h₃⟩ := hMom a ha
  refine ⟨L₃, r₃, C₃, hr₃, fun L hL hLL T hTa hTL hD hS hH hrt hCd => ?_⟩
  obtain ⟨y₃, g₃⟩ := h₃ L hL hLL T hTa hTL hD hS hH hrt hCd
  obtain ⟨y₁, g₁⟩ := hMe T hD hS
  obtain ⟨y₂, g₂⟩ := hLaw T hD hS
  refine ⟨max T.floorMin (max y₁ (max y₂ y₃)), fun y hy hRR hW => ?_⟩
  have hy₀ : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hy₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₂ : y₂ ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hy₃ : y₃ ≤ y := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  obtain ⟨cn, idx, hties, hMA⟩ := g₃ y hy₃ hRR hW
  intro q
  obtain ⟨Ca, hCa⟩ := hMA q
  refine ⟨|Ca|, abs_nonneg _, fun S hS hx0 n _ hn V hV => ?_⟩
  have hadm := hD.fits y hy₀
  have hσ0 : 0 < T.threshold := hD.σ_pos
  have hbig : 4096 ≤ T.n₀ := hD.n₀_ge
  have hn2 : 2 ≤ n := by omega
  have hodd : Odd S.params.side := by
    rw [hS.params_eq]
    exact hD.L_odd
  have hV' : IsCold (9 / 8 * T.threshold) V := fun z μ ν h => by
    have := hV z μ ν h
    linarith
  obtain ⟨e, hmean⟩ := g₁ y hy₁ S hS n hn V hV'
  obtain ⟨hlaw, -⟩ := g₂ y hy₂ S hS n hn V hV'
  obtain ⟨hs, hdens, -⟩ := hF S n V hodd hn2
  have hρ : 0 < S.ballRadius := by
    show 0 < S.params.threshold / 64
    rw [hS.params_eq]
    show 0 < T.threshold / 64
    positivity
  have hgpos : 0 < ∫ η, chartDensity (coldChartSetting S V) η := by
    have h1 := hmean fun _ => 1
    have h2 : ResponseInTheExpansion.coldStepMean S V (fun _ => 1) = 1 := by
      show (∫ k, 1 * (cutoffWeight S.ballRadius S.barrierFn k * Real.exp (- familyLawExponent 1 S.params.coupling S.anchorRadius S.coupling S.frameReach (localFamilyOfDensity S.density) (ResponseInTheExpansion.coldTopField S V) k))) /
        ∫ k, cutoffWeight S.ballRadius S.barrierFn k * Real.exp (- familyLawExponent 1 S.params.coupling S.anchorRadius S.coupling S.frameReach (localFamilyOfDensity S.density) (ResponseInTheExpansion.coldTopField S V) k) = 1
      simp only [one_mul]
      exact div_self hlaw.integral_pos.ne'
    rw [h2] at h1
    have h3 : (∫ η, chartDensity (coldChartSetting S V) η) ≠ 0 := by
      intro h0
      unfold weightedMean at h1
      rw [h0] at h1
      simp at h1
    exact lt_of_le_of_ne (integral_nonneg fun η => chartDensity_nonneg _ η) h3.symm
  have hmom : ∀ b, weightedMean (chartDensity (coldChartSetting S V)) (fun η => ‖η b‖ ^ (2 * q)) ≤ |Ca| * (S.coupling ^ q)⁻¹ := by
    intro b
    have h1 := hmean fun k => ‖k (e b)‖ ^ (2 * q)
    simp only [Equiv.symm_apply_apply] at h1
    rw [h1]
    obtain ⟨ℓ, t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := S
    have e1 : ℓ = T.stepParameters y := hS.params_eq
    have e2 : ρA = T.ρA := hS.anchorRadius_eq
    have e3 : p = T.cutoff := hS.barrierFn_eq
    have hx : y ≤ x := hS.le_coupling
    have hstep := hS.isStep
    subst e1 e2 e3
    have hbelow := hRow (T.stepParameters y) t x D f hadm rfl hstep.1.1
    have hcoldV : IsSmallCurvature T.threshold
        (readAtLevel (torusFrame (T.stepParameters y).side t n) (torusFrame (T.stepParameters y).side t n).top V) := by
      rintro ⟨z, μ, ν⟩ hq
      rw [plaquetteDefect_readAtLevel_eq (period_top_of_extent (F := torusFrame (T.stepParameters y).side t n) (n := n) fun _ => rfl)]
      exact hV (toTorusSite n z) μ ν hq
    have h2 := hCa t x (localFamilyOfDensity f) (torusFrame (T.stepParameters y).side t n)
      (readAtLevel (torusFrame (T.stepParameters y).side t n) (torusFrame (T.stepParameters y).side t n).top V) (e b) hx hbelow
      ⟨rfl, rfl, n, fun _ => rfl, hn⟩ hcoldV
    have hρA : cn.ρA = T.ρA := hties.2.2.1
    have h3 : (coldHalfLawAt (T.stepParamsAt cn idx y) x (localFamilyOfDensity f)).expectation
        (readAtLevel (torusFrame (T.stepParameters y).side t n) (torusFrame (T.stepParameters y).side t n).top V) (fun k => ‖k (e b)‖ ^ (2 * q)) =
        ResponseInTheExpansion.coldStepMean ⟨T.stepParameters y, t, x, x', D, f, Λ, Dq, Φ, φ, T.ρA, T.cutoff⟩ V (fun k => ‖k (e b)‖ ^ (2 * q)) := by
      show ballExpectation (cutoffFactor (T.threshold / 64) T.cutoff) (familyLawExponent 1 T.coupling cn.ρA x (frameRadius x) (localFamilyOfDensity f) _) _ = _
      rw [hρA]
      rfl
    rw [← h3]
    have hx0' : 0 < x := hx0
    exact h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  obtain ⟨hp', hm'⟩ := moments_of_eq_fine_field V q _ _ hs hdens hgpos hmom
  exact ballLaw_of_moments (chartDensity (coldSettingOver S V)) q _ (chartDensity_nonneg _)
    (fun η h => chartDensity_eq_zero_off_balls _ η h) hp' hm'
end YangMills.Construction.MomentLaw
end
