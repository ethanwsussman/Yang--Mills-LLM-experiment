import YangMills.Construction.ClusterExpansionOfAStep.MeanOfTheGainProof
import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.CovarianceInSupNorms
import YangMills.Construction.ClusterExpansionOfAStep.CovarianceOfAFunctionOfSomeBonds
import YangMills.Construction.ClusterExpansionOfAStep.FunctionsNearTheBallsExtend
import YangMills.Construction.ClusterExpansionOfAStep.SecondMomentOfAConvexLaw
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheWeightsOfFreeBonds
import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfTheLawOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames StepSettings TorusLumps TorusFields
namespace ClusterExpansionOfAStep
namespace ConvexLaw
theorem coordNorm_toImaginary (z : EuclideanSpace ℝ (Fin 3)) : coordNorm z = ‖z‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
section Calculus
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem update_add_smul_eq_add_bondVariation (ζ : BondField ι) (b : ι) (X : BondVector) (τ : ℝ) :
    Function.update ζ b (ζ b + τ • X) = ζ + τ • bondVariation b X := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GainMean.update_add_smul_eq <;> assumption
theorem deriv_line_eq_fderiv_of_eventuallyEq {Ψ u : BondField ι → ℝ} (hΨ : Differentiable ℝ Ψ)
    {ζ w : BondField ι} (h : Ψ =ᶠ[nhds ζ] u) :
    deriv (fun t : ℝ => u (ζ + t • w)) 0 = fderiv ℝ Ψ ζ w := by
  have hc : Continuous fun t : ℝ => ζ + t • w :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Filter.Tendsto (fun t : ℝ => ζ + t • w) (nhds 0) (nhds ζ) := by
    simpa using hc.tendsto 0
  have e : (fun t : ℝ => u (ζ + t • w)) =ᶠ[nhds 0] fun t => Ψ (ζ + t • w) :=
    (ht.eventually h).mono fun _ ht' => ht'.symm
  rw [e.deriv_eq]
  have h1 : HasDerivAt (fun t : ℝ => ζ + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add ζ
  have h2 : HasFDerivAt Ψ (fderiv ℝ Ψ ζ) (ζ + (0 : ℝ) • w) := by
    simpa using (hΨ ζ).hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℝ) h1).deriv
theorem bondGradNorm_le_of_slope_le {G' : BondField ι → ℝ} {η : BondField ι} {b : ι} {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ X : BondVector, ‖X‖ = 1 → |fderiv ℝ G' η (bondVariation b X)| ≤ B) :
    bondGradNorm G' b η ≤ B := by
  unfold bondGradNorm
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro e
  by_cases he : e = 0
  · subst he
    simp
  have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr he
  set X := ‖e‖⁻¹ • e with hX
  have u1 : ‖X‖ = 1 := by
    rw [hX, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have e1 : e = ‖e‖ • X := by
    rw [hX, smul_smul, mul_inv_cancel₀ hn, one_smul]
  have e2 : ((fderiv ℝ G' η).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)) e =
      ‖e‖ * fderiv ℝ G' η (bondVariation b X) := by
    conv_lhs => rw [e1]
    rw [map_smul]
    rfl
  rw [e2, norm_mul, norm_norm, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (h X u1) (norm_nonneg _)
theorem ballExpectation_congr {ρ : ℝ} {p : ℝ → ℝ} {Ψ h h' : BondField ι → ℝ}
    (hh : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → h η = h' η) :
    ballExpectation (cutoffFactor ρ p) Ψ h = ballExpectation (cutoffFactor ρ p) Ψ h' := by
  unfold ballExpectation
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  by_cases hz : ∀ b, ‖η b‖ < ρ
  · simp only [hh η hz]
  · push Not at hz
    obtain ⟨b, hb⟩ := hz
    have h0 : ballDensity (cutoffFactor ρ p) Ψ η = 0 := by
      unfold ballDensity radialWeightProd
      rw [Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.mpr hb]), zero_mul]
    simp [h0]
theorem ballCovariance_congr {ρ : ℝ} {p : ℝ → ℝ} {Ψ F F' G G' : BondField ι → ℝ}
    (hF : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → F η = F' η)
    (hG : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → G η = G' η) :
    ballCovariance (cutoffFactor ρ p) Ψ F G = ballCovariance (cutoffFactor ρ p) Ψ F' G' := by
  unfold ballCovariance
  rw [ballExpectation_congr hF, ballExpectation_congr hG,
    ballExpectation_congr fun η hη => by rw [hF η hη, hG η hη]]
end Calculus
end ConvexLaw
open ConvexLaw in
theorem convexLawEstimates_of_convexMeasures (hI : ConvexMeasures.covarianceSupNormBound)
    (hII : ConvexBallLaws.SecondMomentBound) (hIII : ConvexMeasures.covarianceLocalMeasurableBound)
    (hE : BallExtensions.ContDiffExtensionNearBalls) (hCM : ChartPotentialConvex)
    (hW : FreeBondWeightsSummable) : ConvexLawEstimates := by
  intro P lam Cu hσ hrt hlam hCu
  have hW0 : 0 ≤ P.bondWeightBound := by
    unfold StepParameters.bondWeightBound StepParameters.blockBondBound
    positivity
  have hA0 : 0 ≤ P.offDiagonalBound lam Cu := by
    unfold StepParameters.offDiagonalBound StepParameters.blockBondBound
    positivity
  set Wt := P.bondWeightBound with hWt
  set A := P.offDiagonalBound lam Cu with hA
  refine ⟨1 + 8 / lam + 48 * Wt / lam + 64 / lam ^ 2 + 4 * (P.threshold / 64) * (1 + A), by positivity, ?_⟩
  intro y R hR hp hx n _ s u hs
  have hσR : R.params.threshold = P.threshold := by rw [hR]
  have hrtR : R.params.rt = P.rt := by rw [hR]
  have hWR : R.params.bondWeightBound = Wt := by rw [hR]; rfl
  have hAR : R.params.offDiagonalBound lam Cu = A := by rw [hR]; rfl
  have hσ' : 0 < R.params.threshold := hσR ▸ hσ
  have hrt' : 0 < R.params.rt := hrtR ▸ hrt
  have hρ : 0 < R.ballRadius := by
    unfold StepSetup.ballRadius
    positivity
  have hρe : R.ballRadius = P.threshold / 64 := by
    unfold StepSetup.ballRadius
    rw [hσR]
  obtain ⟨Ψ, K, hgerm, hconv, -, hoff⟩ := hCM R lam Cu hσ' hrt' hx hlam n s u hs
  rw [hAR] at hoff
  set m := R.coupling * lam / 8 with hm
  have hm0 : 0 < m := by positivity
  have hd : IsPseudoMetricOnBonds s.bondDist := by
    refine ⟨fun b => ?_, fun b b' => ?_, fun b b' b'' => ?_⟩
    · simp [ChartSetting.bondDist, bondBlockDist, supDist_self]
    · simp only [ChartSetting.bondDist, bondBlockDist]
      rw [supDist_comm]
    · simp only [ChartSetting.bondDist, bondBlockDist]
      exact_mod_cast supDist_triangle _ _ _
  have hin : ∀ η : BondField s.free, (∀ b, ‖η b‖ ≤ R.ballRadius) → s.InBalls η := fun η h b => by
    rw [coordNorm_toImaginary]
    exact h b
  have hin' : ∀ η : BondField s.free, s.InBalls η → ∀ b, ‖η b‖ ≤ R.ballRadius := fun η h b => by
    have := h b
    rwa [coordNorm_toImaginary] at this
  have hopen : ∀ η : BondField s.free, (∀ b, ‖η b‖ < R.ballRadius) → s.InBalls η := fun η h =>
    hin η fun b => (h b).le
  have h00 : s.InBalls (0 : BondField s.free) := hin 0 fun b => by simpa using hρ.le
  have hdens : (fun η => s.cutoffProduct η * Real.exp (-(u η))) =
      ballDensity (cutoffFactor R.ballRadius R.barrierFn) Ψ := by
    funext η
    have e1 : s.cutoffProduct η = radialWeightProd (cutoffFactor R.ballRadius R.barrierFn) η := by
      unfold ChartSetting.cutoffProduct radialWeightProd
      exact Finset.prod_congr rfl fun b _ => by rw [coordNorm_toImaginary]
    unfold ballDensity
    rw [e1]
    by_cases hz : ∀ b, ‖η b‖ < R.ballRadius
    · rw [(hgerm η (hopen η hz)).eq_of_nhds]
    · push Not at hz
      obtain ⟨b, hb⟩ := hz
      have h0 : radialWeightProd (cutoffFactor R.ballRadius R.barrierFn) η = 0 := by
        unfold radialWeightProd
        exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.mpr hb])
      rw [h0, zero_mul, zero_mul]
  have hext : ∀ G : FreeCoords s.free → ℝ, s.IsC1NearBalls G → ∃ G' : BondField s.free → ℝ,
      ContDiff ℝ 1 G' ∧ ∀ η, s.InBalls η → G' =ᶠ[nhds η] G := by
    intro G hG
    obtain ⟨U, hUo, hUb, hUc⟩ := hG
    obtain ⟨G', hG', he⟩ := hE s.free R.ballRadius 1 G U hρ hUo (fun η h => hUb η (hin η h))
      (by exact_mod_cast hUc)
    exact ⟨G', by exact_mod_cast hG', fun η h => he η (hin' η h)⟩
  have hslope : ∀ {G G' : BondField s.free → ℝ} {η : BondField s.free},
      Differentiable ℝ G' → G' =ᶠ[nhds η] G → ∀ (b : s.free) (X : BondVector),
        partialSlope G η b X = fderiv ℝ G' η (bondVariation b X) := by
    intro G G' η hd' hg b X
    unfold partialSlope
    simp only [update_add_smul_eq_add_bondVariation]
    exact deriv_line_eq_fderiv_of_eventuallyEq hd' hg
  have hB0 : ∀ {G : BondField s.free → ℝ} {B : s.free → ℝ}, s.SlopesBoundedBy G B → ∀ b, 0 ≤ B b := by
    intro G B hB b
    have e1 : ‖(EuclideanSpace.single 0 1 : BondVector)‖ = 1 := by simp
    exact (abs_nonneg _).trans (hB 0 h00 b _ e1)
  have hpart : ∀ {G G' : BondField s.free → ℝ} {B : s.free → ℝ}, s.SlopesBoundedBy G B →
      ContDiff ℝ 1 G' → (∀ η, s.InBalls η → G' =ᶠ[nhds η] G) →
      ∀ η : BondField s.free, (∀ b, ‖η b‖ < R.ballRadius) → ∀ b, bondGradNorm G' b η ≤ B b := by
    intro G G' B hB hG' hg η hη b
    refine bondGradNorm_le_of_slope_le (hB0 hB b) fun X hX => ?_
    rw [← hslope (hG'.differentiable (by norm_num)) (hg η (hopen η hη)) b X]
    exact hB η (hopen η hη) b X hX
  set C := 1 + 8 / lam + 48 * Wt / lam + 64 / lam ^ 2 + 4 * (P.threshold / 64) * (1 + A) with hCd
  have hx' : R.coupling ≠ 0 := hx.ne'
  have hl' : lam ≠ 0 := hlam.ne'
  have hC1 : 8 / lam ≤ C := by
    have : 0 ≤ 4 * (P.threshold / 64) * (1 + A) := by positivity
    have h1 : 0 ≤ 48 * Wt / lam := by positivity
    have h2 : 0 ≤ 64 / lam ^ 2 := by positivity
    linarith
  have hC2 : 48 * Wt / lam ≤ C := by
    have : 0 ≤ 4 * (P.threshold / 64) * (1 + A) := by positivity
    have h1 : 0 ≤ 8 / lam := by positivity
    have h2 : 0 ≤ 64 / lam ^ 2 := by positivity
    linarith
  have hC3 : 64 / lam ^ 2 ≤ C := by
    have : 0 ≤ 4 * (P.threshold / 64) * (1 + A) := by positivity
    have h1 : 0 ≤ 8 / lam := by positivity
    have h2 : 0 ≤ 48 * Wt / lam := by positivity
    linarith
  have hC4 : 4 * (P.threshold / 64) * (1 + A) ≤ C := by
    have h1 : 0 ≤ 8 / lam := by positivity
    have h2 : 0 ≤ 48 * Wt / lam := by positivity
    have h3 : 0 ≤ 64 / lam ^ 2 := by positivity
    linarith
  rw [hdens]
  refine ⟨?_, ?_, ?_⟩
  · intro F G BF BG hF hG hbF hbG
    obtain ⟨F', hF', heF⟩ := hext F hF
    obtain ⟨G', hG', heG⟩ := hext G hG
    have hc : weightedCov (ballDensity (cutoffFactor R.ballRadius R.barrierFn) Ψ) F G =
        ballCovariance (cutoffFactor R.ballRadius R.barrierFn) Ψ F' G' :=
      ballCovariance_congr (fun η hη => (heF η (hopen η hη)).eq_of_nhds.symm)
        (fun η hη => (heG η (hopen η hη)).eq_of_nhds.symm)
    rw [hc]
    refine (hI s.free R.ballRadius m R.params.rt s.bondDist Ψ K R.barrierFn hρ hm0 hrt'.le hp hd hconv
      F' G' BF BG hF' hG' (hpart hbF hF' heF) (hpart hbG hG' heG)).trans ?_
    have hS : 0 ≤ ∑ b, ∑ b', BF b * Real.exp (-(R.params.rt * s.bondDist b b')) * BG b' :=
      Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun b' _ =>
        mul_nonneg (mul_nonneg (hB0 hbF b) (Real.exp_pos _).le) (hB0 hbG b')
    have e : m⁻¹ = 8 / lam / R.coupling := by
      rw [hm]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hC1 hx.le) hS
  · intro Aa hAa b
    have hAa0 : ∀ b, 0 ≤ Aa b := by
      intro b
      have e1 : ‖(EuclideanSpace.single 0 1 : BondVector)‖ = 1 := by simp
      exact (abs_nonneg _).trans (hAa b _ e1)
    have hp0 : ∀ b, bondGradNorm Ψ b 0 ≤ Aa b := fun b =>
      bondGradNorm_le_of_slope_le (hAa0 b) fun X hX => by
        rw [← hslope (hconv.smooth.differentiable (by norm_num)) (hgerm 0 h00) b X]
        exact hAa b X hX
    have hmean := hII s.free R.ballRadius m R.params.rt R.params.bondWeightBound s.bondDist Ψ K
      R.barrierFn hρ hm0 hrt'.le hp hd hconv (fun b₀ => hW R hrt' n s b₀) b
    refine le_trans hmean ?_
    rw [hWR]
    apply add_le_add
    · have e : 6 * Wt / m = 48 * Wt / lam / R.coupling := by
        rw [hm]
        field_simp
        ring
      rw [e]
      exact div_le_div_of_nonneg_right hC2 hx.le
    · have e : (m ^ 2)⁻¹ = 64 / lam ^ 2 / R.coupling ^ 2 := by
        rw [hm]
        field_simp
        ring
      rw [e]
      have hsum : ∑ b', Real.exp (-(2 * R.params.rt * s.bondDist b' b)) * bondGradNorm Ψ b' 0 ^ 2 ≤
          ∑ b', Real.exp (-(2 * R.params.rt * s.bondDist b b')) * Aa b' ^ 2 := by
        refine Finset.sum_le_sum fun b' _ => ?_
        rw [hd.symm b' b]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact pow_le_pow_left₀ (norm_nonneg _) (hp0 b') 2
      have hS0 : 0 ≤ ∑ b', Real.exp (-(2 * R.params.rt * s.bondDist b' b)) * bondGradNorm Ψ b' 0 ^ 2 :=
        Finset.sum_nonneg fun b' _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
      exact mul_le_mul (div_le_div_of_nonneg_right hC3 (by positivity)) hsum hS0
        (div_nonneg (hC1.trans' (by positivity) |>.trans le_rfl) (by positivity))
  · intro X F G B O hFm hread hosc hG hbG
    obtain ⟨G', hG', heG⟩ := hext G hG
    have hc : weightedCov (ballDensity (cutoffFactor R.ballRadius R.barrierFn) Ψ) F G =
        ballCovariance (cutoffFactor R.ballRadius R.barrierFn) Ψ F G' :=
      ballCovariance_congr (fun _ _ => rfl) (fun η hη => (heG η (hopen η hη)).eq_of_nhds.symm)
    rw [hc]
    refine (hIII s.free R.ballRadius m R.params.rt A O s.bondDist Ψ K R.barrierFn hρ hm0 hrt'.le hp hd
      hconv hoff X F G' B hFm hread (fun η η' h h' => hosc η η' (hopen η h) (hopen η' h')) hG'
      (hpart hbG hG' heG)).trans ?_
    rw [hρe]
    have hS : 0 ≤ ∑ b ∈ X, ∑ b', B b' * Real.exp (-(R.params.rt * s.bondDist b b')) :=
      Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun b' _ =>
        mul_nonneg (hB0 hbG b') (Real.exp_pos _).le
    have hO : 0 ≤ O := (abs_nonneg _).trans (hosc 0 0 h00 h00)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC4 hO) hS
end ClusterExpansionOfAStep
end YangMills.Construction
end
