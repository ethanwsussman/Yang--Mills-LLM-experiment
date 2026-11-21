import YangMills.Construction.ClusterExpansionOfAStep.LawsOnProductsOfBalls
import YangMills.Construction.SummableBoundsOfTheFlow.LawOfACutIsAProbability
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ConvexObservables
open ColdStepAtMirrorFrames
variable {ρ : ℝ} {p : ℝ → ℝ}
theorem cutoff_nonneg_of_lt (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (hu0 : 0 ≤ u) (huρ : u < ρ) :
    0 ≤ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoff_nonneg_of_lt <;> assumption
theorem cutoffFactor_nonneg (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
theorem cutoffFactor_le_one (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (hu0 : 0 ≤ u) :
    cutoffFactor ρ p u ≤ 1 := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_le_one <;> assumption
theorem cutoffFactor_pos {u : ℝ} (huρ : u < ρ) : 0 < cutoffFactor ρ p u := by
  unfold cutoffFactor
  rw [if_pos huρ]
  exact Real.exp_pos _
theorem cutoffFactor_eq_zero {u : ℝ} (hρu : ρ ≤ u) : cutoffFactor ρ p u = 0 := by
  unfold cutoffFactor
  rw [if_neg (not_lt.mpr hρu)]
theorem measurable_cutoffFactor_norm (hp : IsCutoff ρ p) :
    Measurable fun e : BondVector => cutoffFactor ρ p ‖e‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.measurable_cutoffFactor_norm <;> assumption
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Ψ : BondField ι → ℝ}
theorem ballDensity_eq (η : BondField ι) :
    ballDensity (cutoffFactor ρ p) Ψ η = (∏ b, cutoffFactor ρ p ‖η b‖) * Real.exp (-Ψ η) := rfl
theorem measurable_ballDensity (hp : IsCutoff ρ p) (hΨ : Continuous Ψ) :
    Measurable (ballDensity (cutoffFactor ρ p) Ψ) := by
  have hprod : Measurable fun η : BondField ι => ∏ b, cutoffFactor ρ p ‖η b‖ :=
    Finset.measurable_fun_prod _ fun b _ => (measurable_cutoffFactor_norm hp).comp (measurable_pi_apply b)
  have hexp : Measurable fun η : BondField ι => Real.exp (-Ψ η) :=
    (Real.continuous_exp.comp hΨ.neg).measurable
  exact hprod.mul hexp
theorem ballDensity_nonneg (η : BondField ι) : 0 ≤ ballDensity (cutoffFactor ρ p) Ψ η := by
  rw [ballDensity_eq]
  exact mul_nonneg (Finset.prod_nonneg fun _ _ => cutoffFactor_nonneg _) (Real.exp_pos _).le
theorem norm_lt_of_ballDensity_ne_zero {η : BondField ι}
    (hne : ballDensity (cutoffFactor ρ p) Ψ η ≠ 0) : ∀ b, ‖η b‖ < ρ := by
  intro b
  by_contra hb
  apply hne
  rw [ballDensity_eq, Finset.prod_eq_zero (Finset.mem_univ b) (cutoffFactor_eq_zero (not_lt.mp hb)), zero_mul]
theorem ballDensity_pos {η : BondField ι} (hin : ∀ b, ‖η b‖ < ρ) :
    0 < ballDensity (cutoffFactor ρ p) Ψ η := by
  rw [ballDensity_eq]
  exact mul_pos (Finset.prod_pos fun b _ => cutoffFactor_pos (hin b)) (Real.exp_pos _)
theorem isCompact_closedBalls : IsCompact {η : BondField ι | ∀ b, ‖η b‖ ≤ ρ} := by
  have : {η : BondField ι | ∀ b, ‖η b‖ ≤ ρ} =
      Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : BondVector) ρ := by
    ext η
    simp [Set.mem_pi]
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
theorem integrable_ballDensity (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hΨ : Continuous Ψ) :
    Integrable (ballDensity (cutoffFactor ρ p) Ψ) := by
  set K := {η : BondField ι | ∀ b, ‖η b‖ ≤ ρ} with hK
  have hKc : IsCompact K := isCompact_closedBalls
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn
    (f := fun η => Real.exp (-Ψ η)) (Real.continuous_exp.comp hΨ.neg).continuousOn
  have hind : Integrable (K.indicator fun _ => B) := by
    apply IntegrableOn.integrable_indicator _ hKc.measurableSet
    exact integrableOn_const hKc.measure_lt_top.ne
  refine hind.mono' (measurable_ballDensity hp hΨ).aestronglyMeasurable (ae_of_all _ fun η => ?_)
  rw [Real.norm_of_nonneg (ballDensity_nonneg η)]
  by_cases hη : η ∈ K
  · rw [Set.indicator_of_mem hη, ballDensity_eq]
    have hprod : ∏ b, cutoffFactor ρ p ‖η b‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => cutoffFactor_nonneg _) fun b _ =>
        cutoffFactor_le_one hρ hp (norm_nonneg _)
    have hbound := hB η hη
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hbound
    calc (∏ b, cutoffFactor ρ p ‖η b‖) * Real.exp (-Ψ η) ≤ 1 * Real.exp (-Ψ η) :=
          mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
      _ ≤ B := by rw [one_mul]; exact hbound
  · rw [Set.indicator_of_notMem hη]
    obtain ⟨b, hb⟩ : ∃ b, ρ < ‖η b‖ := by
      by_contra hcon
      push_neg at hcon
      exact hη hcon
    rw [ballDensity_eq, Finset.prod_eq_zero (Finset.mem_univ b) (cutoffFactor_eq_zero hb.le), zero_mul]
theorem integral_ballDensity_pos (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hΨ : Continuous Ψ) :
    0 < ∫ ζ, ballDensity (cutoffFactor ρ p) Ψ ζ := by
  rw [integral_pos_iff_support_of_nonneg (fun η => ballDensity_nonneg η) (integrable_ballDensity hρ hp hΨ)]
  have hopen : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by
    have : {η : BondField ι | ∀ b, ‖η b‖ < ρ} = ⋂ b, {η | ‖η b‖ < ρ} := by
      ext η
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun b =>
      isOpen_lt ((continuous_norm.comp (continuous_apply b))) continuous_const
  have hvol : 0 < volume {η : BondField ι | ∀ b, ‖η b‖ < ρ} :=
    hopen.measure_pos _ ⟨0, fun b => by simpa using hρ⟩
  refine hvol.trans_le (measure_mono ?_)
  intro η hη
  exact (ballDensity_pos hη).ne'
theorem cutoffFactor_antitone (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) :
    cutoffFactor ρ p v ≤ cutoffFactor ρ p u := by
  by_cases hvρ : v < ρ
  · have huρ : u < ρ := lt_of_le_of_lt huv hvρ
    rw [cutoffFactor, cutoffFactor, if_pos hvρ, if_pos huρ]
    apply Real.exp_le_exp.mpr
    have hpv := cutoff_nonneg_of_lt hρ hp (hu0.trans huv) hvρ
    rcases eq_or_lt_of_le (hu0.trans huv) with hv0 | hvpos
    · have : u = v := by linarith
      rw [this]
    have hp0 : p 0 = 0 := hp.vanish_small 0 le_rfl (by positivity)
    have hwa : 0 ≤ 1 - u / v := by
      rw [sub_nonneg, div_le_one hvpos]
      exact huv
    have hwb : 0 ≤ u / v := div_nonneg hu0 hvpos.le
    have hconv := hp.convex.2 (show (0 : ℝ) ∈ Set.Ico 0 ρ from ⟨le_rfl, hρ⟩)
      (show v ∈ Set.Ico 0 ρ from ⟨hu0.trans huv, hvρ⟩) hwa hwb (by ring)
    have hpoint : (1 - u / v) • (0 : ℝ) + (u / v) • v = u := by
      simp only [smul_eq_mul, mul_zero, zero_add]
      field_simp
    rw [hpoint, hp0] at hconv
    simp only [smul_eq_mul, mul_zero, zero_add] at hconv
    have hle : u / v * p v ≤ p v := by
      have : u / v ≤ 1 := (div_le_one hvpos).mpr huv
      nlinarith
    linarith
  · rw [cutoffFactor_eq_zero (not_lt.mp hvρ)]
    exact cutoffFactor_nonneg _
theorem continuousOn_ballDensity (hp : IsCutoff ρ p) (hΨ : Continuous Ψ) :
    ContinuousOn (ballDensity (cutoffFactor ρ p) Ψ) {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by
  have hcut : ContinuousOn (cutoffFactor ρ p) (Set.Ico 0 ρ) := by
    have hexp : ContinuousOn (fun u => Real.exp (-p u)) (Set.Ico 0 ρ) :=
      Real.continuous_exp.comp_continuousOn hp.smooth.continuousOn.neg
    refine hexp.congr fun u hu => ?_
    simp only [cutoffFactor, if_pos hu.2]
  have hfac : ∀ b : ι, ContinuousOn (fun η : BondField ι => cutoffFactor ρ p ‖η b‖)
      {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by
    intro b
    refine hcut.comp (continuous_norm.comp (continuous_apply b)).continuousOn ?_
    intro η hη
    exact ⟨norm_nonneg _, hη b⟩
  have hprod : ContinuousOn (fun η : BondField ι => ∏ b, cutoffFactor ρ p ‖η b‖)
      {η : BondField ι | ∀ b, ‖η b‖ < ρ} := continuousOn_finsetProd _ fun b _ => hfac b
  exact hprod.mul (Real.continuous_exp.comp hΨ.neg).continuousOn
theorem normalizedBallLaw_isProbability : normalizedBallLawIsProbabilityStatement := by
  intro ι _ _ ρ p Ψ hρ hp hΨ
  have hZ := integral_ballDensity_pos hρ hp hΨ
  have hint := integrable_ballDensity hρ hp hΨ
  have hmeas := measurable_ballDensity hp hΨ
  set Z := ∫ ζ, ballDensity (cutoffFactor ρ p) Ψ ζ with hZdef
  have hg : Measurable fun η => ENNReal.ofReal (ballDensity (cutoffFactor ρ p) Ψ η / Z) :=
    (hmeas.div_const Z).ennreal_ofReal
  refine ⟨⟨?_⟩, ?_, ?_, ?_, hmeas, fun η => ballDensity_nonneg η, hint, hZ,
    continuousOn_ballDensity hp hΨ,
    fun η => ⟨norm_lt_of_ballDensity_ne_zero, fun h => (ballDensity_pos h).ne'⟩,
    fun u v hu0 huv => cutoffFactor_antitone hρ hp hu0 huv⟩
  · unfold normalizedBallLaw
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hint.div_const Z)
        (ae_of_all _ fun η => div_nonneg (ballDensity_nonneg η) hZ.le), integral_div, ← hZdef,
      div_self hZ.ne', ENNReal.ofReal_one]
  · intro f
    unfold normalizedBallLaw ballExpectation
    rw [integral_withDensity_eq_integral_toReal_smul hg (ae_of_all _ fun η => ENNReal.ofReal_lt_top),
      ← hZdef, ← integral_div]
    apply integral_congr_ae
    filter_upwards with η
    rw [ENNReal.toReal_ofReal (div_nonneg (ballDensity_nonneg η) hZ.le), smul_eq_mul]
    ring
  · intro f
    unfold normalizedBallLaw
    rw [integrable_withDensity_iff hg (ae_of_all _ fun η => ENNReal.ofReal_lt_top)]
    have hfun : (fun η => f η * (ENNReal.ofReal (ballDensity (cutoffFactor ρ p) Ψ η / Z)).toReal) =
        fun η => (f η * ballDensity (cutoffFactor ρ p) Ψ η) / Z := by
      funext η
      rw [ENNReal.toReal_ofReal (div_nonneg (ballDensity_nonneg η) hZ.le)]
      ring
    rw [hfun]
    constructor
    · intro h
      have := h.mul_const Z
      refine this.congr (ae_of_all _ fun η => ?_)
      simp only
      field_simp
    · intro h
      exact h.div_const Z
  · unfold normalizedBallLaw
    rw [ae_withDensity_iff hg]
    refine ae_of_all _ fun η hη => ?_
    apply norm_lt_of_ballDensity_ne_zero (p := p) (Ψ := Ψ)
    intro h0
    apply hη
    rw [h0]
    simp
end YangMills.Construction.ConvexObservables
end
