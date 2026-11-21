import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.FourPointCondition.EvaluationAtTheBareLevel
import YangMills.Construction.FourPointCondition.LawsAtTheBareLevel
import YangMills.Construction.FourPointCondition.ObservablesOfTheExpansionCoincide
import YangMills.Construction.FourPointCondition.TuplesCarriedToASide
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
namespace YangMills.Construction
open PeriodicLattice WeightedResponses ResponseInTheExpansion TorusFields FourPointBounds Cumulants
namespace FourPointCondition
private theorem mixedCumulant_map_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω'} {Φ : Ω' → Ω}
    (hΦ : Measurable Φ) {k : ℕ} {X : Fin k → Ω → ℝ} (hX : ∀ i, Measurable (X i)) :
    mixedCumulant (μ.map Φ) X = mixedCumulant μ fun i => X i ∘ Φ := by
  have e : (fun t : Fin k → ℂ => Complex.log (momentGeneratingFunction (μ.map Φ) X t)) =
      fun t => Complex.log (momentGeneratingFunction μ (fun i => X i ∘ Φ) t) := by
    funext t
    congr 1
    unfold momentGeneratingFunction
    refine integral_map hΦ.aemeasurable ?_
    have : Measurable fun ω => Complex.exp (∑ i, t i * (X i ω : ℂ)) := by
      refine Complex.measurable_exp.comp (Finset.measurable_sum _ fun i _ => ?_)
      exact measurable_const.mul (Complex.measurable_ofReal.comp (hX i))
    exact this.aestronglyMeasurable
  unfold mixedCumulant
  rw [e]
private theorem measurable_curvatureObservable {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    Measurable (curvatureObservable (m := m) h) := by
  unfold curvatureObservable
  refine Finset.measurable_sum _ fun p _ => measurable_const.mul ?_
  exact (continuous_plaquetteEnergy p.1 p.2.1 p.2.2).measurable
private theorem torusSide_div_levelMesh (L m K : ℕ) (hL : 0 < L) :
    torusSide L m / levelMesh L K 0 = 2 * (L : ℝ) ^ (m + K) := by
  unfold levelMesh meshSize torusSide
  have e : -(((K : ℤ) - ((0 : ℕ) : ℤ))) = -(K : ℤ) := by simp
  rw [e, zpow_neg, zpow_natCast, div_inv_eq_mul, pow_add]
  ring
theorem cumulantLawsAtBareLevel_holds (hRd : fineLevelQuadraticApproxStatement)
    (hCu : cumulantOfQuadraticApproximationStatement)
    (hCN : CutoffRescalingInvariance) (hOb : torusUrsellEqWeightedCurvatureStatement)
    (hTu : dilatedTupleToSideStatement) : cumulantLawsAtBareLevel := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hr, H⟩ := hRd a ha
  refine ⟨L₀, rt₀, C₀, hr, fun L hodd hL Tb hTa hTL hD hC hHf hrt hc => ?_⟩
  obtain ⟨y₀, Hy⟩ := H L hodd hL Tb hTa hTL hD hC hHf hrt hc
  refine ⟨y₀, fun y hy hR hW => ?_⟩
  obtain ⟨hadm, Hr⟩ := Hy y hy hR hW
  intro vt hv0 hv1
  obtain ⟨Cr, C, x₀, Hv⟩ := Hr vt hv0 hv1
  obtain ⟨C1, x1, h1⟩ := hCu 1 Cr (fun _ => C) C le_rfl (by norm_num)
  obtain ⟨C3, x3, h3⟩ := hCu 3 Cr (fun _ => C) C (by norm_num) le_rfl
  refine ⟨|C1| + |C3| + |C|, max (max x₀ (max x1 x3)) (Real.exp 1), fun β hβ K m d hside hn1 hn2 => ?_⟩
  have hx₀ : x₀ ≤ β := ((le_max_left _ _).trans (le_max_left _ _)).trans hβ
  have hx1 : x1 ≤ β := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hβ
  have hx3 : x3 ≤ β := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hβ
  have hβe : Real.exp 1 ≤ β := (le_max_right _ _).trans hβ
  have hβ1 : 1 ≤ β := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hβ0 : 0 < β := by linarith
  have hlog : 1 ≤ Real.log β := (Real.le_log_iff_exp_le hβ0).2 hβe
  have hLge : 2 ^ 16 ≤ (Tb.stepParameters y).side := hadm.L_ge
  have hLpos : 0 < (Tb.stepParameters y).side := by omega
  have hL3 : 3 ≤ (Tb.stepParameters y).side := by omega
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = d / levelMesh (Tb.stepParameters y).side K 0 := ⟨_, rfl⟩
  rw [← hn] at hn1 hn2 ⊢
  rw [torusSide_div_levelMesh _ _ _ hLpos] at hside
  have hM1 : 1 ≤ m + K := by
    by_contra hcon
    have h0 : m + K = 0 := by omega
    rw [h0, pow_zero, mul_one] at hside
    have h2 : Real.exp 1 ≤ Real.exp (Real.log β ^ 3) := by
      refine Real.exp_le_exp.2 ?_
      exact one_le_pow₀ hlog
    have h3 := Real.exp_one_gt_d9
    linarith
  have heq : n * torusSide (Tb.stepParameters y).side m = d * torusSide (Tb.stepParameters y).side (m + K) := by
    have e2 : torusSide (Tb.stepParameters y).side (m + K) =
        torusSide (Tb.stepParameters y).side m / levelMesh (Tb.stepParameters y).side K 0 := by
      rw [torusSide_div_levelMesh _ _ _ hLpos]
      rfl
    rw [hn, e2]
    ring
  intro q hq f hf
  obtain ⟨htup, hlaw⟩ := hTu (Tb.stepParameters y) m (m + K) (q + 1) d n vt hadm heq f hf
  have hlaw := hlaw q rfl f hf
  obtain ⟨g, hg⟩ : ∃ g : Fin (q + 1) → FourTorus (Tb.stepParameters y).side (m + K) → ℝ,
      g = fun i => dilateToSide (Tb.stepParameters y).side m (m + K) (f i) := ⟨_, rfl⟩
  rw [← hg] at htup hlaw
  have hS : torusUrsellFunction (Tb.stepParameters y).side m K β f =
      connectedCurvature β (fineSide (Tb.stepParameters y).side 0 (2 * (Tb.stepParameters y).side ^ (m + K)))
        (fun i => testWeight (Tb.stepParameters y).side 0 (m + K) (g i)) := by
    rw [hCN (Tb.stepParameters y).side m K (m + K) 0 (q + 1) β hL3 (by omega) f, ← hg]
    exact hOb (Tb.stepParameters y).side (m + K) 0 (q + 1) β hL3 hM1 g
  obtain ⟨Ω, _, μ, _, Φ, I, _, G, A, B, κ, Tc, Bg, hΦ, hmap, R, hFb, hLp⟩ :=
    Hv q β (m + K) n hq hx₀ hside hn1 hn2 g htup
  have hcum : connectedCurvature β (fineSide (Tb.stepParameters y).side 0 (2 * (Tb.stepParameters y).side ^ (m + K)))
        (fun i => testWeight (Tb.stepParameters y).side 0 (m + K) (g i)) =
      mixedCumulant μ fun i ω => curvatureObservable (testWeight (Tb.stepParameters y).side 0 (m + K) (g i)) (Φ ω) := by
    unfold connectedCurvature
    rw [← hmap]
    exact mixedCumulant_map_eq hΦ fun i => measurable_curvatureObservable _
  have hn4 : n ^ 4 ≤ β := by
    have h2 : n ^ 4 ≤ (β ^ ((1 : ℝ) / 90)) ^ 4 := pow_le_pow_left₀ (by linarith) hn2 4
    refine h2.trans ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul hβ0.le]
    calc β ^ ((1 : ℝ) / 90 * ((4 : ℕ) : ℝ)) ≤ β ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hβ1 (by norm_num)
      _ = β := Real.rpow_one β
  have hFm : ∀ i, Measurable fun ω => curvatureObservable (testWeight (Tb.stepParameters y).side 0 (m + K) (g i)) (Φ ω) :=
    fun i => (measurable_curvatureObservable _).comp hΦ
  have hFbd : ∀ i, ∃ Cb : ℝ, ∀ᵐ ω ∂μ,
      |curvatureObservable (testWeight (Tb.stepParameters y).side 0 (m + K) (g i)) (Φ ω)| ≤ Cb :=
    fun i => ⟨C * n ^ 4, ae_of_all _ fun ω => hFb i ω⟩
  have hFmom : ∀ i (r : ℕ), 1 ≤ r →
      ∫ ω, |curvatureObservable (testWeight (Tb.stepParameters y).side 0 (m + K) (g i)) (Φ ω) - (0 : Fin (q + 1) → ℝ) i| ^ (2 * r) ∂μ ≤
        ((fun _ : ℕ => C) r * n ^ 4) ^ (2 * r) := by
    intro i r _
    have hb : ∀ ω, |curvatureObservable (testWeight (Tb.stepParameters y).side 0 (m + K) (g i)) (Φ ω) - (0 : Fin (q + 1) → ℝ) i| ^ (2 * r) ≤
        (C * n ^ 4) ^ (2 * r) := by
      intro ω
      simp only [Pi.zero_apply, sub_zero]
      exact pow_le_pow_left₀ (abs_nonneg _) (hFb i ω) _
    have h2 := integral_mono_of_nonneg (μ := μ) (ae_of_all _ fun ω => pow_nonneg (abs_nonneg _) _)
      (integrable_const ((C * n ^ 4) ^ (2 * r))) (ae_of_all _ hb)
    refine h2.trans (le_of_eq ?_)
    simp
  have hcore : ‖(β : ℂ) ^ (q + 1) * mixedCumulant μ
        (fun i ω => curvatureObservable (testWeight (Tb.stepParameters y).side 0 (m + K) (g i)) (Φ ω)) -
      ((cyclicTraceSum κ Tc : ℝ) : ℂ)‖ ≤ (|C1| + |C3|) * β ^ (-(1 / 5 : ℝ)) := by
    have hp : 0 ≤ β ^ (-(1 / 5 : ℝ)) := Real.rpow_nonneg hβ0.le _
    rcases hq with rfl | rfl
    · refine (h1 Ω μ I _ G A B κ Tc 0 0 β n (n ^ 4) Bg hx1 hn1 hn2 (by positivity) hn4 R hFm hFbd hFmom).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self C1, abs_nonneg C3]) hp
    · refine (h3 Ω μ I _ G A B κ Tc 0 0 β n (n ^ 4) Bg hx3 hn1 hn2 (by positivity) hn4 R hFm hFbd hFmom).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self C3, abs_nonneg C1]) hp
  rw [hS, hcum, one_pow, one_mul, ← hlaw]
  have hp1 : β ^ (-(1 / 5 : ℝ)) ≤ β ^ (-(1 / 100 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hβ1 (by norm_num)
  have hp0 : 0 ≤ β ^ (-(1 / 100 : ℝ)) := Real.rpow_nonneg hβ0.le _
  have hn0 : 0 ≤ 1 / n := by
    have : 0 < n := by linarith
    positivity
  have htri : ‖((β ^ (q + 1) : ℝ) : ℂ) * mixedCumulant μ
        (fun i ω => curvatureObservable (testWeight (Tb.stepParameters y).side 0 (m + K) (g i)) (Φ ω)) -
      ((gaussianCumulantLimit (torusSide (Tb.stepParameters y).side (m + K)) g : ℝ) : ℂ)‖ ≤
      ‖(β : ℂ) ^ (q + 1) * mixedCumulant μ
        (fun i ω => curvatureObservable (testWeight (Tb.stepParameters y).side 0 (m + K) (g i)) (Φ ω)) -
      ((cyclicTraceSum κ Tc : ℝ) : ℂ)‖ +
        |cyclicTraceSum κ Tc - gaussianCumulantLimit (torusSide (Tb.stepParameters y).side (m + K)) g| := by
    have e : ((β ^ (q + 1) : ℝ) : ℂ) = (β : ℂ) ^ (q + 1) := by push_cast; rfl
    rw [e]
    have e2 : |cyclicTraceSum κ Tc - gaussianCumulantLimit (torusSide (Tb.stepParameters y).side (m + K)) g| =
        ‖((cyclicTraceSum κ Tc : ℝ) : ℂ) - ((gaussianCumulantLimit (torusSide (Tb.stepParameters y).side (m + K)) g : ℝ) : ℂ)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [e2]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  refine htri.trans ?_
  have hc1 := abs_nonneg C1
  have hc3 := abs_nonneg C3
  have hcc := abs_nonneg C
  have hle : C ≤ |C| := le_abs_self C
  have t1 : (|C1| + |C3|) * β ^ (-(1 / 5 : ℝ)) ≤ (|C1| + |C3|) * (β ^ (-(1 / 100 : ℝ)) + 1 / n) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have t2 : C * (β ^ (-(1 / 100 : ℝ)) + 1 / n) ≤ |C| * (β ^ (-(1 / 100 : ℝ)) + 1 / n) :=
    mul_le_mul_of_nonneg_right hle (by linarith)
  calc _ ≤ (|C1| + |C3|) * β ^ (-(1 / 5 : ℝ)) + C * (β ^ (-(1 / 100 : ℝ)) + 1 / n) := add_le_add hcore hLp
    _ ≤ _ := by linarith
end FourPointCondition
end YangMills.Construction
end
