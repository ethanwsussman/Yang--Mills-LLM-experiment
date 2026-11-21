import YangMills.Construction.ColdStepAtMirrorFrames.MeanDensityOnOneTorusForm
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfTheStepAreSmooth
import YangMills.Construction.ColdStepAtMirrorFrames.SizesOfTheMeanDensity
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetweenProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages DerivativeInterpolation SummableBounds
namespace ColdStepAtMirrorFrames
namespace InteractionDensityBounds
variable {F : BlockFrame}
theorem bondDeriv_zero {j : ℕ} (g : F.GaugeField j → ℝ) (U : F.GaugeField j) (b : Fin 0 → F.Site j × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) : bondDeriv g U b X = g U := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
theorem exp_decay_interpolation_le {κ c τ : ℝ} {r k : ℕ} (hκ : 0 < κ) (hc : 0 < c) (hτ : 0 < τ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
    c * Real.exp (-(κ * r / 2 ^ 7)) / τ ^ k +
        (c * Real.exp (-(κ * r / 2 ^ 7))) ^ (1 - (k : ℝ) / 3) * c ^ ((k : ℝ) / 3) ≤
      c * (1 + 1 / τ + (1 / τ) ^ 2) * Real.exp (-(κ / 2 ^ 9 * r)) := by apply _root_.YangMills.Construction.InterpolatedBirths.interpolation_sum_le <;> assumption
end InteractionDensityBounds
open InteractionDensityBounds in
theorem interactionDensityBounds_holds (hJ : EventuallyInParametersCombines)
    (hDrawn : joinAtLoweredSmallnessConstantStatement)
    (hOne : interactionDensityOnTorusStatement) (hSm : meansContDiffThree)
    (hMeans : covarianceBoundsStatement) (hTwo : DerivDiffLeOfCloseAlongLines)
    (hLines : SmallCurvatureAlongLineAndAgreeOn) :
    interactionDensityBoundsStatement := by
  obtain ⟨join, -⟩ := hJ
  obtain ⟨Ct, hCt, hTw⟩ := hTwo
  refine hDrawn (fun T => InteractionDensityEstimatesAt T ∧ MeansContDiffThreeAt T) CovarianceBoundsAt _
    (fun T c => c * (1 + Ct * (1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2)))
    (join _ _ hOne hSm) hMeans fun T c hc hL hn₁ hy hE hη hη' hκ hσ hchain hcut hG hP hR => ?_
  obtain ⟨hPb, hPs⟩ := hP
  have hG' : c * (1 + Ct * (1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2)) ≤ T.Cs := hG
  have hc0 : 0 < c := by linarith
  have hτ : 0 < T.σ / 64 := by positivity
  have hcC : c ≤ T.Cs := by
    refine le_trans ?_ hG'
    have : 0 ≤ c * (Ct * (1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2)) := by positivity
    nlinarith
  have hmono : ∀ {j : ℕ} {F : BlockFrame} {W : F.GaugeField j}, IsSmallCurvature (9 / 8 * T.σ) W →
      IsSmallCurvature (5 / 4 * T.σ) W := fun h p hp => (h p hp).trans_le (by nlinarith)
  intro t x hx f hf
  have hPb' := hPb t x hx f hf
  have hPs' := hPs t x hx f hf
  refine ⟨fun F hF Y V hV => (hPb' F hF Y V (hmono hV)).1.trans hcC, ?_, ?_⟩
  · intro F hF Y V k c' X hV h1 h3 hX
    exact ((hPb' F hF Y V (hmono hV)).2.1 k c' X h1 h3 hX).trans
      (mul_le_mul_of_nonneg_right hcC (Real.exp_pos _).le)
  · intro F F' hF hF' Y Y' V V' r k h X hV hV' hag hk hbox hX
    have hval : ∀ (W : F.GaugeField F.top) (W' : F'.GaugeField F'.top), IsSmallCurvature (5 / 4 * T.σ) W →
        IsSmallCurvature (5 / 4 * T.σ) W' → AgreeOnBall (finiteCells F) W (finiteCells F') W' Y Y' r →
        |T.interactionFamily x f F Y W - T.interactionFamily x f F' Y' W'| ≤ c * Real.exp (-(T.κ * r / 2 ^ 7)) := by
      intro W W' hW hW' hagW
      have hfr := (hR t x f F W hx hf hF hW false).2 F' W' Y Y' r hF' hW' hagW
      let G : ℝ → ℝ := fun v => cutoffMean T.ballRadius T.p
        (fun η => v * stepExponent false T.a T.chainParams.ρA x (frameRadius x) f 0 W η +
          (1 - v) * totalQuadratic T.chainParams.lam x η)
        (fun η => cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y W η -
          cellQuadratic T.chainParams.lam x Y η)
      let G' : ℝ → ℝ := fun v => cutoffMean T.ballRadius T.p
        (fun η => v * stepExponent false T.a T.chainParams.ρA x (frameRadius x) f 0 W' η +
          (1 - v) * totalQuadratic T.chainParams.lam x η)
        (fun η => cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y' W' η -
          cellQuadratic T.chainParams.lam x Y' η)
      have hI : IntervalIntegrable G MeasureTheory.volume 0 1 := (hPb' F hF Y W hW).2.2
      have hI' : IntervalIntegrable G' MeasureTheory.volume 0 1 := (hPb' F' hF' Y' W' hW').2.2
      have e : T.interactionFamily x f F Y W - T.interactionFamily x f F' Y' W' =
          ∫ v in (0 : ℝ)..1, (G' v - G v) := by
        rw [intervalIntegral.integral_sub hI' hI]
        show (-∫ v in (0 : ℝ)..1, G v) - (-∫ v in (0 : ℝ)..1, G' v) = _
        ring
      have hb : ‖∫ v in (0 : ℝ)..1, (G' v - G v)‖ ≤ c * Real.exp (-(T.κ * r / 2 ^ 7)) * |(1 : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun v hv => by
          rw [Set.uIoc_of_le zero_le_one] at hv
          rw [Real.norm_eq_abs, abs_sub_comm]
          exact (hfr v hv.1.le hv.2).1
      have h10 : |(1 : ℝ) - 0| = 1 := by norm_num
      rw [e, ← Real.norm_eq_abs]
      rw [h10, mul_one] at hb
      exact hb
    set E₁ := Real.exp (-(T.κ / 2 ^ 9 * r)) with hE₁
    have hE₁0 : 0 < E₁ := Real.exp_pos _
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [bondDeriv_zero, bondDeriv_zero]
      refine (hval V V' (hmono hV) (hmono hV') hag).trans ?_
      have hE : Real.exp (-(T.κ * r / 2 ^ 7)) ≤ E₁ := by
        apply Real.exp_le_exp.mpr
        have e : T.κ / 2 ^ 9 * r = T.κ * r / 2 ^ 9 := by ring
        have hr : 0 ≤ T.κ * r := by positivity
        rw [e]
        nlinarith
      exact mul_le_mul hcC hE (Real.exp_pos _).le (by linarith)
    · have hk2 : k ≤ 2 := hk
      have hM₀ : 0 < c * Real.exp (-(T.κ * r / 2 ^ 7)) := by positivity
      have hmove : ∀ (ς : Fin k → ℝ), (∀ l, ς l = 1 ∨ ς l = -1) → ∀ l, ‖ς l • X l‖ = 1 := by
        intro ς hς l
        rw [norm_smul, hX l, mul_one]
        rcases hς l with h1 | h1 <;> simp [h1]
      have hline : ∀ {F₁ : BlockFrame} (V₁ : F₁.GaugeField F₁.top) (c₁ : Fin k → F₁.Site F₁.top × Fin 4)
          (X₁ : Fin k → imaginaryQuaternions) (s : ℝ),
          (∀ l, ‖X₁ l‖ = 1) → |s| ≤ T.σ / 64 → IsSmallCurvature (9 / 8 * T.σ) V₁ →
          IsSmallCurvature (5 / 4 * T.σ) (alongLine c₁ X₁ s V₁) := by
        intro F₁ V₁ c₁ X₁ s hu hs hV₁ p hp
        have h1 := hLines.1 F₁ V₁ k c₁ X₁ s (9 / 8 * T.σ) (fun l => (hu l).le) hV₁ p hp
        refine h1.trans_le ?_
        have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
        nlinarith
      have hread : ∀ (F₁ : BlockFrame), IsCubicTopTorus T.L t T.n₀ F₁ → ∀ (Y₁ : F₁.Cell) (V₁ : F₁.GaugeField F₁.top)
          (c₁ : Fin k → F₁.Site F₁.top × Fin 4) (X₁ : Fin k → imaginaryQuaternions), (∀ l, ‖X₁ l‖ = 1) →
          IsSmallCurvature (9 / 8 * T.σ) V₁ →
          IsControlledAlongLine (T.interactionFamily x f F₁ Y₁) V₁ c₁ X₁ (T.σ / 64) c := by
        intro F₁ hF₁ Y₁ V₁ c₁ X₁ hu hV₁
        refine ⟨fun s hs => (hPs' F₁ hF₁ Y₁ _ (hline V₁ c₁ X₁ s hu hs hV₁)).1, fun s hs e => ?_⟩
        have h1 := (hPb' F₁ hF₁ Y₁ _ (hline V₁ c₁ X₁ s hu hs hV₁)).2.1 3 (c₁ ∘ e) (X₁ ∘ e) (by norm_num) le_rfl
          (fun l => hu (e l))
        refine h1.trans ?_
        have he : Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y₁ (c₁ ∘ e))) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          have : 0 ≤ T.κ / 2 ^ 6 * bondSpan Y₁ (c₁ ∘ e) := by positivity
          linarith
        calc c * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y₁ (c₁ ∘ e))) ≤ c * 1 := mul_le_mul_of_nonneg_left he hc0.le
          _ = c := mul_one c
      have h1 := hTw F F' (T.interactionFamily x f F Y) (T.interactionFamily x f F' Y') V V' k (bondsAt Y h) (bondsAt Y' h) X
        (T.σ / 64) (c * Real.exp (-(T.κ * r / 2 ^ 7))) c hk0 hk2 hτ hM₀ hc0.le (fun ς hς =>
          ⟨hread F hF Y V _ _ (hmove ς hς) hV, hread F' hF' Y' V' _ _ (hmove ς hς) hV', fun s hs =>
            hval _ _ (hline V _ _ s (hmove ς hς) hs hV) (hline V' _ _ s (hmove ς hς) hs hV')
              (hLines.2 F F' V V' Y Y' r k h _ s hag hbox)⟩)
      refine h1.trans ?_
      have h2 := exp_decay_interpolation_le (r := r) hκ hc0 hτ hk0 hk2
      calc Ct * (c * Real.exp (-(T.κ * r / 2 ^ 7)) / (T.σ / 64) ^ k +
            (c * Real.exp (-(T.κ * r / 2 ^ 7))) ^ (1 - (k : ℝ) / 3) * c ^ ((k : ℝ) / 3))
          ≤ Ct * (c * (1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2) * E₁) :=
            mul_le_mul_of_nonneg_left h2 hCt.le
        _ ≤ c * (1 + Ct * (1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2)) * E₁ := by
            have : 0 ≤ c * E₁ := by positivity
            nlinarith
        _ ≤ T.Cs * E₁ := mul_le_mul_of_nonneg_right hG' hE₁0.le
end ColdStepAtMirrorFrames
end YangMills.Construction
end
