import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesAtARadiusWithNoLevel
import YangMills.Construction.SixteenPointsOnASmallTorus.MeanOfTheCopiesAtNoLevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
private theorem curvatureObservable_translateWeight_neg {m : ℕ} [NeZero m] (u : TorusFields.TorusSite m)
    (w : WeightedResponses.PlaquetteWeight m) (U : TorusFields.TorusField m) :
    WeightedResponses.curvatureObservable (WeightedResponses.translateWeight (-u) w) U =
      WeightedResponses.curvatureObservable w (TorusFields.translate u U) := by
  classical
  unfold WeightedResponses.curvatureObservable
  refine Finset.sum_bij' (fun p _ => (p.1 - u, p.2)) (fun p _ => (p.1 + u, p.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [TorusFields.plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and, implies_true, and_true] at hp ⊢
    exact hp
  · intro p hp
    simp only [TorusFields.plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and, implies_true, and_true] at hp ⊢
    exact hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    simp only [WeightedResponses.translateWeight, WeightedResponses.plaquetteEnergyOf, TorusFields.plaquetteEnergy_translate]
    simp [sub_eq_add_neg]
abbrev _root_.YangMills.SharedProofs.p30727 := @curvatureObservable_translateWeight_neg
private theorem isProbabilityMeasure_wilsonLaw (β : ℝ) (m : ℕ) [NeZero m] :
    IsProbabilityMeasure (WeightedResponses.wilsonLaw β m) := by
  constructor
  have hc : Continuous fun U : TorusFields.TorusField m => Real.exp (-β * TorusFields.wilsonAction Finset.univ U) :=
    Real.continuous_exp.comp (continuous_const.mul (TorusFields.continuous_wilsonAction _))
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hI : Integrable (fun U : TorusFields.TorusField m => Real.exp (-β * TorusFields.wilsonAction Finset.univ U))
      (TorusFields.fieldHaar m) :=
    Integrable.of_bound hc.measurable.aestronglyMeasurable B (Filter.Eventually.of_forall fun U => hB U (Set.mem_univ _))
  have hZ : 0 < ∫ U, Real.exp (-β * TorusFields.wilsonAction Finset.univ U) ∂(TorusFields.fieldHaar m) :=
    integral_exp_pos hI
  unfold WeightedResponses.wilsonLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hI.div_const _)
      (Filter.Eventually.of_forall fun U => div_nonneg (Real.exp_nonneg _) hZ.le),
    integral_div, div_self hZ.ne', ENNReal.ofReal_one]
abbrev _root_.YangMills.SharedProofs.p1521 := @isProbabilityMeasure_wilsonLaw
theorem reflectedMeanWithoutLevel_of (hbound : copyBoundWithoutLevelStatement) :
    reflectedMeanWithoutLevelStatement := by
  intro a ha
  obtain ⟨L₀, r₀, C₀, hr₀, h⟩ := hbound a ha
  refine ⟨L₀, r₀, C₀, hr₀, fun L hL hLL T hTa hTL hD hC hO hr' hCd => ?_⟩
  obtain ⟨y₀, hy⟩ := h L hL hLL T hTa hTL hD hC hO hr' hCd
  refine ⟨y₀, fun y hy₀ hr hw Ξ hΞ => ?_⟩
  obtain ⟨C, hC0, hCb⟩ := hy y hy₀ hr hw Ξ hΞ
  refine ⟨C, hC0, fun β K κ ρ H Λ f hset hκ hρ hρ' hS hlev z => ?_⟩
  have := isProbabilityMeasure_wilsonLaw β (2 * T.side ^ κ)
  have hH : 0 ≤ H := (abs_nonneg _).trans (hS.abs_le 0)
  set Q : ℝ := C * (1 + TorusBound.logPos (1 / ρ)) ^ ((1 : ℝ) / 25) * H with hQ
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ TorusBound.logPos (1 / ρ) := le_max_right _ _
    have h2 : 0 ≤ (1 + TorusBound.logPos (1 / ρ)) ^ ((1 : ℝ) / 25) := Real.rpow_nonneg (by linarith) _
    positivity
  have hb : ∀ U : TorusFields.TorusField (2 * T.side ^ κ),
      ‖∏ k : Fin 4 → Fin 2, (WeightedResponses.curvatureObservable
        (reflectedWeightAbout (levelSpacing T.side K 0) (T.side ^ κ) z (fun μ => (k μ : ℕ)) f) U - 0)‖ ≤ Q ^ 16 := by
    intro U
    rw [norm_prod]
    calc ∏ k : Fin 4 → Fin 2, ‖WeightedResponses.curvatureObservable
            (reflectedWeightAbout (levelSpacing T.side K 0) (T.side ^ κ) z (fun μ => (k μ : ℕ)) f) U - 0‖
        ≤ ∏ _k : Fin 4 → Fin 2, Q := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => ?_
          rw [sub_zero, Real.norm_eq_abs]
          unfold reflectedWeightAbout
          rw [curvatureObservable_translateWeight_neg]
          exact hCb β K κ ρ H Λ f hset hκ hρ hρ' hS hlev k _
      _ = Q ^ 16 := by simp
  have hn := norm_integral_le_of_norm_le_const (μ := WeightedResponses.wilsonLaw β (2 * T.side ^ κ))
    (Filter.Eventually.of_forall hb)
  have hu : (WeightedResponses.wilsonLaw β (2 * T.side ^ κ)).real Set.univ = 1 := by simp
  rw [hu, mul_one] at hn
  exact (le_abs_self _).trans hn
end YangMills.Construction.SmallTorusCopies
end
