import YangMills.Construction.ClusterExpansionOfAStep.FactorOfAClassIsOneRuleProof
import YangMills.Construction.SummableBoundsOfTheFlow.FloorOfTheScaledExponentsProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledLawsTendToTheirGaussians
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames MeasureTheory
open scoped Topology
namespace YangMills.Construction.ScaledVariables
section GaussianTail
variable {ι : Type} [Fintype ι]
private theorem integrable_poly_mul_exp_neg_quadratic {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (M : ℕ) :
    Integrable (fun x : BondField ι =>
      (1 + ‖x‖) ^ M * Real.exp (-(a * ∑ b, ‖x b‖ ^ 2 - c * ∑ b, ‖x b‖))) := by
  obtain ⟨J, hJ⟩ := exists_nat_gt (Module.finrank ℝ (BondField ι) : ℝ)
  have hint : Integrable (fun x : BondField ι => (1 + ‖x‖) ^ (-(J : ℝ))) volume :=
    integrable_one_add_norm hJ
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  set D : ℝ := c * n + ((M : ℝ) + J) with hD
  refine (hint.const_mul (Real.exp (D ^ 2 / (4 * a)))).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · refine Filter.Eventually.of_forall fun x => ?_
    set u : ℝ := ‖x‖ with hu
    have hu0 : 0 ≤ u := norm_nonneg _
    have hsq_le : u ^ 2 ≤ ∑ b, ‖x b‖ ^ 2 := by
      have hle : u ≤ Real.sqrt (∑ b, ‖x b‖ ^ 2) := by
        refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun b => ?_
        refine Real.le_sqrt_of_sq_le ?_
        exact Finset.single_le_sum (f := fun b => ‖x b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)
      have := Real.sq_sqrt (Finset.sum_nonneg fun b (_ : b ∈ Finset.univ) => by positivity : 0 ≤ ∑ b, ‖x b‖ ^ 2)
      nlinarith [Real.sqrt_nonneg (∑ b, ‖x b‖ ^ 2)]
    have hsum_le : ∑ b, ‖x b‖ ≤ n * u := by
      calc ∑ b, ‖x b‖ ≤ ∑ _b : ι, u := Finset.sum_le_sum fun b _ => norm_le_pi_norm x b
        _ = n * u := by simp [hn]
    have h1u : 0 < 1 + u := by linarith
    have hexp : Real.exp (-(a * ∑ b, ‖x b‖ ^ 2 - c * ∑ b, ‖x b‖)) ≤ Real.exp (-(a * u ^ 2) + c * n * u) := by
      apply Real.exp_le_exp.2
      nlinarith [mul_le_mul_of_nonneg_left hsq_le ha.le, mul_le_mul_of_nonneg_left hsum_le hc]
    have hpow : (1 + u) ^ (M + J) ≤ Real.exp (((M : ℝ) + J) * u) := by
      have e : Real.exp (((M : ℝ) + J) * u) = Real.exp u ^ (M + J) := by
        rw [← Real.exp_nat_mul]
        push_cast
        rfl
      rw [e]
      exact pow_le_pow_left₀ h1u.le (by linarith [Real.add_one_le_exp u]) _
    have hquad : -(a * u ^ 2) + D * u ≤ D ^ 2 / (4 * a) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2 * a * u - D)]
    have hrpow : (1 + u) ^ (-(J : ℝ)) = ((1 + u) ^ J)⁻¹ := by
      rw [Real.rpow_neg h1u.le, Real.rpow_natCast]
    rw [hrpow, Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc (1 + u) ^ M * Real.exp (-(a * ∑ b, ‖x b‖ ^ 2 - c * ∑ b, ‖x b‖)) * (1 + u) ^ J
        = (1 + u) ^ (M + J) * Real.exp (-(a * ∑ b, ‖x b‖ ^ 2 - c * ∑ b, ‖x b‖)) := by
          rw [pow_add]; ring
      _ ≤ Real.exp (((M : ℝ) + J) * u) * Real.exp (-(a * u ^ 2) + c * n * u) :=
          mul_le_mul hpow hexp (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (-(a * u ^ 2) + D * u) := by
          rw [← Real.exp_add, hD]
          ring_nf
      _ ≤ Real.exp (D ^ 2 / (4 * a)) := Real.exp_le_exp.2 hquad
abbrev _root_.YangMills.SharedProofs.p40209 := @integrable_poly_mul_exp_neg_quadratic
end GaussianTail
private theorem tendsto_integral_ratio {E : Type} [MeasurableSpace E] {μ : Measure E} {l₀ : ℝ} (hl₀ : 0 < l₀)
    {A H : ℝ → E → ℝ} {A₀ H₀ G B : E → ℝ}
    (hAm : ∀ l, 0 < l → l ≤ l₀ → AEStronglyMeasurable (A l) μ)
    (hHm : ∀ l, 0 < l → l ≤ l₀ → AEStronglyMeasurable (H l) μ)
    (hAG : ∀ l, 0 < l → l ≤ l₀ → ∀ x, ‖A l x‖ ≤ G x)
    (hHB : ∀ l, 0 < l → l ≤ l₀ → ∀ x, ‖H l x * A l x‖ ≤ B x)
    (hG : Integrable G μ) (hB : Integrable B μ)
    (hA : ∀ x, Filter.Tendsto (fun l => A l x) (𝓝[>] 0) (𝓝 (A₀ x)))
    (hH : ∀ x, Filter.Tendsto (fun l => H l x) (𝓝[>] 0) (𝓝 (H₀ x)))
    (hne : (∫ x, A₀ x ∂μ) ≠ 0) :
    Filter.Tendsto (fun l => (∫ x, H l x * A l x ∂μ) / ∫ x, A l x ∂μ) (𝓝[>] 0)
      (𝓝 ((∫ x, H₀ x * A₀ x ∂μ) / ∫ x, A₀ x ∂μ)) := by
  have hev : ∀ᶠ l in 𝓝[>] (0 : ℝ), 0 < l ∧ l ≤ l₀ := by
    filter_upwards [Ioc_mem_nhdsGT hl₀] with l hl using hl
  refine Filter.Tendsto.div ?_ ?_ hne
  · refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hB ?_
    · filter_upwards [hev] with l hl using (hHm l hl.1 hl.2).mul (hAm l hl.1 hl.2)
    · filter_upwards [hev] with l hl
      exact Filter.Eventually.of_forall (hHB l hl.1 hl.2)
    · exact Filter.Eventually.of_forall fun x => (hH x).mul (hA x)
  · refine tendsto_integral_filter_of_dominated_convergence G ?_ ?_ hG ?_
    · filter_upwards [hev] with l hl using hAm l hl.1 hl.2
    · filter_upwards [hev] with l hl
      exact Filter.Eventually.of_forall (hAG l hl.1 hl.2)
    · exact Filter.Eventually.of_forall hA
variable {F : BlockFrame}
private theorem cutoffFactor_nonneg (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
private theorem cutoffFactor_le_one {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 ≤ u) :
    cutoffFactor ρ p u ≤ 1 := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_le_one <;> assumption
private theorem cutoffWeight_nonneg (ρ : ℝ) (p : ℝ → ℝ) (η : StepVariable (finiteCells F)) : 0 ≤ cutoffWeight ρ p η :=
  Finset.prod_nonneg fun _ _ => cutoffFactor_nonneg _ _ _
private theorem cutoffWeight_le_one {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (η : StepVariable (finiteCells F)) :
    cutoffWeight ρ p η ≤ 1 :=
  Finset.prod_le_one (fun _ _ => cutoffFactor_nonneg _ _ _) fun _ _ => cutoffFactor_le_one hρ hp (norm_nonneg _)
private theorem cutoffWeight_eq_zero {ρ : ℝ} {p : ℝ → ℝ} {η : StepVariable (finiteCells F)}
    {b : ↥(chordBonds (finiteCells F))} (h : ρ ≤ ‖η b‖) : cutoffWeight ρ p η = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.2 h])
private theorem cutoffWeight_eq_one {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) {η : StepVariable (finiteCells F)}
    (h : ∀ b, ‖η b‖ ≤ 5 * ρ / 8) : cutoffWeight ρ p η = 1 :=
  Finset.prod_eq_one fun b _ => by
    unfold cutoffFactor
    rw [if_pos (by linarith [h b]), hp.vanish_small _ (norm_nonneg _) (h b)]
    simp
private theorem measurable_cutoffWeight {ρ : ℝ} {p : ℝ → ℝ} (hp : IsCutoff ρ p) :
    Measurable (cutoffWeight (F := F) ρ p) := by
  classical
  have hc : ContinuousOn (fun u => Real.exp (-p u)) (Set.Ico 0 ρ) := hp.smooth.continuousOn.neg.rexp
  have hm : Measurable ((Set.Ico 0 ρ).piecewise (fun u => Real.exp (-p u)) (fun _ => (0 : ℝ))) :=
    hc.measurable_piecewise continuousOn_const measurableSet_Ico
  unfold cutoffWeight
  refine Finset.measurable_prod _ fun b _ => ?_
  have e : (fun η : StepVariable (finiteCells F) => cutoffFactor ρ p ‖η b‖) = fun η =>
      (Set.Ico 0 ρ).piecewise (fun u => Real.exp (-p u)) (fun _ => (0 : ℝ)) ‖η b‖ := by
    funext η
    by_cases h : ‖η b‖ < ρ
    · rw [Set.piecewise_eq_of_mem (Set.Ico 0 ρ) _ _ (⟨norm_nonneg _, h⟩ : ‖η b‖ ∈ Set.Ico 0 ρ)]
      simp [cutoffFactor, h]
    · rw [Set.piecewise_eq_of_notMem (Set.Ico 0 ρ) _ _ (fun hh : ‖η b‖ ∈ Set.Ico 0 ρ => h hh.2)]
      simp [cutoffFactor, h]
  rw [e]
  exact hm.comp (measurable_pi_apply b).norm
private def rescaledDensity (ρ l : ℝ) (p : ℝ → ℝ) (Ψ : StepVariable (finiteCells F) → ℝ)
    (ζ : StepVariable (finiteCells F)) : ℝ :=
  cutoffWeight ρ p (l • ζ) * Real.exp (-(Ψ (l • ζ) - Ψ 0))
private theorem cutoffMean_eq_ratio_rescaled (ρ : ℝ) (p : ℝ → ℝ) (Ψ H : StepVariable (finiteCells F) → ℝ) {l : ℝ} (hl : 0 < l) :
    cutoffMean ρ p Ψ (fun η => H (l⁻¹ • η)) =
      (∫ ζ, H ζ * rescaledDensity ρ l p Ψ ζ) / ∫ ζ, rescaledDensity ρ l p Ψ ζ := by
  set c : ℝ := |(l ^ Module.finrank ℝ (StepVariable (finiteCells F)))⁻¹| with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact abs_ne_zero.2 (inv_ne_zero (pow_ne_zero _ hl.ne'))
  have hsub : ∀ g : StepVariable (finiteCells F) → ℝ, ∫ ζ, g (l • ζ) = c * ∫ η, g η := fun g => by
    rw [Measure.integral_comp_smul, smul_eq_mul]
  have hnum : (∫ ζ, H ζ * rescaledDensity ρ l p Ψ ζ) = Real.exp (Ψ 0) *
      (c * ∫ η, H (l⁻¹ • η) * (cutoffWeight ρ p η * Real.exp (-Ψ η))) := by
    rw [← hsub (fun η => H (l⁻¹ • η) * (cutoffWeight ρ p η * Real.exp (-Ψ η))), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    simp only [rescaledDensity, inv_smul_smul₀ hl.ne']
    rw [show -(Ψ (l • ζ) - Ψ 0) = -Ψ (l • ζ) + Ψ 0 by ring, Real.exp_add]
    ring
  have hden : (∫ ζ, rescaledDensity ρ l p Ψ ζ) = Real.exp (Ψ 0) *
      (c * ∫ η, cutoffWeight ρ p η * Real.exp (-Ψ η)) := by
    rw [← hsub (fun η => cutoffWeight ρ p η * Real.exp (-Ψ η)), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    simp only [rescaledDensity]
    rw [show -(Ψ (l • ζ) - Ψ 0) = -Ψ (l • ζ) + Ψ 0 by ring, Real.exp_add]
    ring
  unfold cutoffMean
  rw [hnum, hden, mul_div_mul_left _ _ (Real.exp_pos _).ne', mul_div_mul_left _ _ hc0]
private theorem eventually_mul_norm_lt {r : ℝ} (hr : 0 < r) (ζ : StepVariable (finiteCells F)) :
    ∀ᶠ l in 𝓝[>] (0 : ℝ), 0 < l ∧ ∀ b, l * ‖ζ b‖ < r := by apply _root_.YangMills.SharedProofs.p61909 <;> assumption
private theorem tendsto_cutoffMean_rescaled {ρ lam l₀ K : ℝ} {M : ℕ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (hlam : 0 < lam) (hl₀ : 0 < l₀) {Ψ U H : ℝ → StepVariable (finiteCells F) → ℝ}
    {H₀ : StepVariable (finiteCells F) → ℝ}
    (hfl : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → l ≤ l₀ → MemScaledBalls ρ l ζ →
      lam / 4 * ∑ b, ‖ζ b‖ ^ 2 - Real.sqrt lam / 2 * ∑ b, ‖ζ b‖ ≤ U l ζ - U l 0)
    (hid : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → l ≤ l₀ → MemScaledBalls ρ l ζ →
      Ψ l (l • ζ) = U l ζ)
    (hct : ∀ l : ℝ, 0 < l → l ≤ l₀ → ContinuousOn (U l) {ζ | MemScaledBalls ρ l ζ})
    (hlim : ∀ ζ : StepVariable (finiteCells F), Filter.Tendsto (fun l => U l ζ) (𝓝[>] 0) (𝓝 (U 0 ζ)))
    (hHm : ∀ l : ℝ, 0 < l → l ≤ l₀ → Measurable (H l))
    (hHb : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → l ≤ l₀ → MemScaledBalls ρ l ζ →
      |H l ζ| ≤ K * (1 + ‖ζ‖) ^ M)
    (hHl : ∀ ζ : StepVariable (finiteCells F), Filter.Tendsto (fun l => H l ζ) (𝓝[>] 0) (𝓝 (H₀ ζ))) :
    Filter.Tendsto (fun l => cutoffMean ρ p (Ψ l) fun η => H l (l⁻¹ • η)) (𝓝[>] 0)
      (𝓝 ((∫ ζ, H₀ ζ * Real.exp (-(U 0 ζ - U 0 0))) / ∫ ζ, Real.exp (-(U 0 ζ - U 0 0)))) := by
  classical
  set G : StepVariable (finiteCells F) → ℝ := fun ζ =>
    Real.exp (-(lam / 4 * ∑ b, ‖ζ b‖ ^ 2 - Real.sqrt lam / 2 * ∑ b, ‖ζ b‖)) with hG
  set A : ℝ → StepVariable (finiteCells F) → ℝ := fun l => rescaledDensity ρ l p (Ψ l) with hA
  set W : StepVariable (finiteCells F) → ℝ := fun ζ => Real.exp (-(U 0 ζ - U 0 0)) with hW
  have hz : ∀ l : ℝ, MemScaledBalls ρ l (0 : StepVariable (finiteCells F)) := fun l b => by simpa using hρ
  have hAin : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → l ≤ l₀ → MemScaledBalls ρ l ζ →
      A l ζ = cutoffWeight ρ p (l • ζ) * Real.exp (-(U l ζ - U l 0)) := by
    intro l ζ h0 hl hζ
    have e0 := hid l 0 h0 hl (hz l)
    rw [smul_zero] at e0
    simp only [hA, rescaledDensity, hid l ζ h0 hl hζ, e0]
  have hAout : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → ¬ MemScaledBalls ρ l ζ → A l ζ = 0 := by
    intro l ζ h0 hζ
    unfold MemScaledBalls at hζ
    simp only [not_forall, not_lt] at hζ
    obtain ⟨b, hb⟩ := hζ
    have hb' : ρ ≤ ‖(l • ζ) b‖ := by
      rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg h0.le]
      exact hb
    simp only [hA, rescaledDensity, cutoffWeight_eq_zero hb', zero_mul]
  have hA0 : ∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 ≤ A l ζ := fun l ζ =>
    mul_nonneg (cutoffWeight_nonneg _ _ _) (Real.exp_pos _).le
  have hAG : ∀ l : ℝ, 0 < l → l ≤ l₀ → ∀ ζ, A l ζ ≤ G ζ := by
    intro l h0 hl ζ
    by_cases hζ : MemScaledBalls ρ l ζ
    · rw [hAin l ζ h0 hl hζ]
      calc cutoffWeight ρ p (l • ζ) * Real.exp (-(U l ζ - U l 0))
          ≤ 1 * Real.exp (-(U l ζ - U l 0)) :=
            mul_le_mul_of_nonneg_right (cutoffWeight_le_one hρ hp _) (Real.exp_pos _).le
        _ ≤ G ζ := by
            rw [one_mul]
            exact Real.exp_le_exp.2 (neg_le_neg (hfl l ζ h0 hl hζ))
    · rw [hAout l ζ h0 hζ]
      exact (Real.exp_pos _).le
  have hAm : ∀ l : ℝ, 0 < l → l ≤ l₀ → Measurable (A l) := by
    intro l h0 hl
    have hB : MeasurableSet {ζ : StepVariable (finiteCells F) | MemScaledBalls ρ l ζ} := by
      have e : {ζ : StepVariable (finiteCells F) | MemScaledBalls ρ l ζ} = ⋂ b, {ζ | l * ‖ζ b‖ < ρ} := by
        ext ζ
        simp [MemScaledBalls]
      rw [e]
      exact MeasurableSet.iInter fun b =>
        measurableSet_lt ((measurable_pi_apply b).norm.const_mul l) measurable_const
    have hc : ContinuousOn (fun ζ => Real.exp (-(U l ζ - U l 0))) {ζ | MemScaledBalls ρ l ζ} :=
      ((hct l h0 hl).sub continuousOn_const).neg.rexp
    have hm := hc.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const hB
    have hr : Measurable fun ζ : StepVariable (finiteCells F) => cutoffWeight ρ p (l • ζ) :=
      (measurable_cutoffWeight hp).comp (continuous_const_smul l).measurable
    have e : A l = fun ζ => cutoffWeight ρ p (l • ζ) *
        Set.piecewise {ζ | MemScaledBalls ρ l ζ} (fun ζ => Real.exp (-(U l ζ - U l 0))) (fun _ => (0 : ℝ)) ζ := by
      funext ζ
      by_cases hζ : MemScaledBalls ρ l ζ
      · rw [hAin l ζ h0 hl hζ, Set.piecewise_eq_of_mem _ _ _ (show ζ ∈ {ζ | MemScaledBalls ρ l ζ} from hζ)]
      · rw [hAout l ζ h0 hζ, Set.piecewise_eq_of_notMem _ _ _ (show ζ ∉ {ζ | MemScaledBalls ρ l ζ} from hζ),
          mul_zero]
    rw [e]
    exact hr.mul hm
  have hAl : ∀ ζ, Filter.Tendsto (fun l => A l ζ) (𝓝[>] 0) (𝓝 (W ζ)) := by
    intro ζ
    have hsm : ∀ᶠ l in 𝓝[>] (0 : ℝ), Real.exp (-(U l ζ - U l 0)) = A l ζ := by
      have h58 : 0 < 5 * ρ / 8 := by positivity
      filter_upwards [eventually_mul_norm_lt h58 ζ, Ioc_mem_nhdsGT hl₀] with l h1 h2
      have hin : MemScaledBalls ρ l ζ := fun b => by linarith [h1.2 b]
      rw [hAin l ζ h1.1 h2.2 hin, cutoffWeight_eq_one hρ hp, one_mul]
      intro b
      rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg h1.1.le]
      exact (h1.2 b).le
    exact Filter.Tendsto.congr' hsm
      ((Real.continuous_exp.tendsto _).comp ((hlim ζ).sub (hlim 0)).neg)
  have hq : 0 < lam / 4 := by positivity
  have hs : 0 ≤ Real.sqrt lam / 2 := by positivity
  have hGi : Integrable G := by
    simpa [hG] using integrable_poly_mul_exp_neg_quadratic (ι := ↥(chordBonds (finiteCells F))) hq hs 0
  have hWle : ∀ ζ, W ζ ≤ G ζ := fun ζ => by
    refine le_of_tendsto (hAl ζ) ?_
    filter_upwards [Ioc_mem_nhdsGT hl₀] with l hl using hAG l hl.1 hl.2 ζ
  have hWm : AEStronglyMeasurable W volume := by
    let u : ℕ → ℝ := fun n => l₀ * (1 / ((n : ℝ) + 1))
    have hu0 : ∀ n, 0 < u n := fun n => by positivity
    have hu1 : ∀ n, u n ≤ l₀ := fun n => by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      nlinarith
    have hu : Filter.Tendsto u Filter.atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall hu0⟩
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul l₀
      rw [mul_zero] at h
      exact h
    exact aestronglyMeasurable_of_tendsto_ae Filter.atTop (f := fun n => A (u n))
      (fun n => (hAm (u n) (hu0 n) (hu1 n)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ζ => (hAl ζ).comp hu)
  have hWi : Integrable W := hGi.mono' hWm (Filter.Eventually.of_forall fun ζ => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hWle ζ)
  have hWpos : 0 < ∫ ζ, W ζ := by
    rw [integral_pos_iff_support_of_nonneg (fun ζ => (Real.exp_pos _).le) hWi]
    have e : Function.support W = Set.univ := by
      ext ζ
      simp [hW, (Real.exp_pos _).ne']
    rw [e]
    exact isOpen_univ.measure_pos volume Set.univ_nonempty
  have hBi : Integrable (fun ζ : StepVariable (finiteCells F) => |K| * ((1 + ‖ζ‖) ^ M * G ζ)) :=
    (integrable_poly_mul_exp_neg_quadratic (ι := ↥(chordBonds (finiteCells F))) hq hs M).const_mul |K|
  have hHB : ∀ l : ℝ, 0 < l → l ≤ l₀ → ∀ ζ, ‖H l ζ * A l ζ‖ ≤ |K| * ((1 + ‖ζ‖) ^ M * G ζ) := by
    intro l h0 hl ζ
    by_cases hζ : MemScaledBalls ρ l ζ
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (hA0 l ζ)]
      have h1 : |H l ζ| ≤ |K| * (1 + ‖ζ‖) ^ M :=
        (hHb l ζ h0 hl hζ).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
      calc |H l ζ| * A l ζ ≤ (|K| * (1 + ‖ζ‖) ^ M) * G ζ :=
            mul_le_mul h1 (hAG l h0 hl ζ) (hA0 l ζ) (by positivity)
        _ = |K| * ((1 + ‖ζ‖) ^ M * G ζ) := by ring
    · rw [hAout l ζ h0 hζ, mul_zero, norm_zero]
      have : 0 ≤ G ζ := (Real.exp_pos _).le
      positivity
  have hr := tendsto_integral_ratio (μ := volume) hl₀ (A := A) (H := H) (A₀ := W) (H₀ := H₀) (G := G)
    (fun l h0 hl => (hAm l h0 hl).aestronglyMeasurable) (fun l h0 hl => (hHm l h0 hl).aestronglyMeasurable)
    (fun l h0 hl ζ => by
      rw [Real.norm_of_nonneg (hA0 l ζ)]
      exact hAG l h0 hl ζ) hHB hGi hBi hAl hHl hWpos.ne'
  refine hr.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hl₀] with l hl
  exact (cutoffMean_eq_ratio_rescaled ρ p (Ψ l) (H l) hl.1).symm
theorem scaledLawsTendToGaussian_of_rescaledExponentFloor (hFl : rescaledExponentFloorStatement) :
    scaledLawsTendToGaussian := by
  refine EventuallyOrdered.mono hFl fun T hT hn h => ?_
  intro e
  obtain ⟨l₀, hl₀, g⟩ := h e
  refine ⟨l₀, hl₀, ?_⟩
  intro t f F V law H H₀ K m hf hFt hV hlaw hHm hHb hHl
  obtain ⟨hfl, hid, hct, hlim⟩ := g t f F V law hf hFt hV hlaw
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold YangMills.Construction.ColdStepAtMirrorFrames.StepParameters.ballRadius
    positivity
  have hlam : 0 < T.lam := hT.chain_admissible.positivity.2.2.1
  exact tendsto_cutoffMean_rescaled hρ hT.cutoff hlam hl₀
    (Ψ := fun l => stepLawExponent T.a T.ρA T.lam (l⁻¹ ^ 2) f V law)
    (U := fun l => rescaledLawExponent T.a T.ρA T.lam f l V law) (H := H) (H₀ := H₀)
    (fun l ζ h0 hl hζ => hfl l ζ h0.le hl hζ) hid hct hlim hHm hHb hHl
end YangMills.Construction.ScaledVariables
end
