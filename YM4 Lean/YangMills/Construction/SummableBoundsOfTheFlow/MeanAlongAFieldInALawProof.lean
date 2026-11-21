import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACut
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongAFieldInALaw
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongAFieldProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.BondIntegration
namespace AlongField
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ}
theorem hasDerivAt_cutoffFactor_line (hρ : 0 < ρ) (hp : IsCutoff ρ p) {v : BondVector} (hv : ‖v‖ < ρ)
    (e : BondVector) :
    HasDerivAt (fun τ : ℝ => cutoffFactor ρ p ‖v + τ • e‖)
      (-(cutoffFactor ρ p ‖v‖ * radialCutoffSlope p v e)) 0 := by apply _root_.YangMills.Construction.BondIntegration.hasDerivAt_cutoffFactor_line <;> assumption
theorem add_smul_bondVariation_apply (η : BondField ι) (b : ι) (e : BondVector) (τ : ℝ) (b' : ι) :
    (η + τ • bondVariation b e) b' = if b' = b then η b + τ • e else η b' := by apply _root_.YangMills.Construction.BondIntegration.add_smul_bondVariation_apply <;> assumption
theorem hasDerivAt_ballDensity_line (hρ : 0 < ρ) (hp : IsCutoff ρ p) {Ψ : BondField ι → ℝ}
    {η : BondField ι} (hη : ∀ b, ‖η b‖ < ρ) (hΨ : DifferentiableAt ℝ Ψ η) (b : ι) (e : BondVector) :
    HasDerivAt (fun τ : ℝ => ballDensity (cutoffFactor ρ p) Ψ (η + τ • bondVariation b e))
      (-(ballDensity (cutoffFactor ρ p) Ψ η *
        (fderiv ℝ Ψ η (bondVariation b e) + radialCutoffSlope p (η b) e))) 0 := by apply _root_.YangMills.Construction.BondIntegration.hasDerivAt_ballDensity_line <;> assumption
def smoothStep (t : ℝ) : ℝ := Real.smoothTransition (t - 1)
theorem contDiff_smoothStep : ContDiff ℝ 1 smoothStep := by
  unfold smoothStep
  exact Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
theorem smoothStep_of_le_one {t : ℝ} (h : t ≤ 1) : smoothStep t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
theorem smoothStep_of_two_le {t : ℝ} (h : 2 ≤ t) : smoothStep t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
theorem abs_smoothStep_le_one (t : ℝ) : |smoothStep t| ≤ 1 := by
  show |Real.smoothTransition (t - 1)| ≤ 1
  rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _
theorem deriv_smoothStep_of_lt_or_gt {t : ℝ} (h : t < 1 ∨ 2 < t) : deriv smoothStep t = 0 := by
  rcases h with h | h
  · have e : smoothStep =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with u hu
      exact smoothStep_of_le_one (le_of_lt hu)
    rw [e.deriv_eq]
    simp
  · have e : smoothStep =ᶠ[nhds t] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with u hu
      exact smoothStep_of_two_le (le_of_lt hu)
    rw [e.deriv_eq]
    simp
theorem exists_abs_deriv_smoothStep_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ t, |deriv smoothStep t| ≤ K := by
  have hc : Continuous (deriv smoothStep) := contDiff_smoothStep.continuous_deriv le_rfl
  obtain ⟨K, hK⟩ :=
    (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|K|, abs_nonneg _, fun t => ?_⟩
  by_cases h : t ∈ Set.Icc (1 : ℝ) 2
  · exact (by simpa using hK t h : |deriv smoothStep t| ≤ K).trans (le_abs_self K)
  · have : t < 1 ∨ 2 < t := by
      by_contra h'
      push Not at h'
      exact h h'
    rw [deriv_smoothStep_of_lt_or_gt this]
    simp
def levelCutoff (ρ : ℝ) (p : ℝ → ℝ) (ε : ℝ) (v : BondVector) : ℝ :=
  smoothStep (cutoffFactor ρ p ‖v‖ / ε)
theorem contDiff_cutoffFactor_norm (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) :
    ContDiff ℝ 1 (fun v : BondVector => cutoffFactor ρ p ‖v‖) := by
  have hW := hR ρ p hρ hp
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases h0 : v = 0
  · subst h0
    have hev : (fun v : BondVector => cutoffFactor ρ p ‖v‖) =ᶠ[nhds 0] fun _ => 1 := by
      have hlt : ∀ᶠ v : BondVector in nhds 0, ‖v‖ < 5 * ρ / 8 := by
        have hc : Continuous fun v : BondVector => ‖v‖ := continuous_norm
        exact hc.continuousAt.eventually_lt continuousAt_const (by simp; positivity)
      filter_upwards [hlt] with v hv
      have := hW.one ‖v‖ (norm_nonneg _) hv.le
      simpa [max_eq_left (norm_nonneg v)] using this
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have h1 : ContDiffAt ℝ 1 (fun v : BondVector => ‖v‖) v := contDiffAt_norm ℝ h0
    have h2 := hW.smooth.contDiffAt.comp v h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    simp [max_eq_left (norm_nonneg w)]
theorem contDiff_levelCutoff (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (ε : ℝ) :
    ContDiff ℝ 1 (levelCutoff ρ p ε) := by
  unfold levelCutoff
  exact contDiff_smoothStep.comp ((contDiff_cutoffFactor_norm hR hρ hp).div_const ε)
theorem cutoffFactor_norm_of_le {v : BondVector} (h : ρ ≤ ‖v‖) : cutoffFactor ρ p ‖v‖ = 0 := by
  unfold cutoffFactor
  rw [if_neg (not_lt.2 h)]
theorem cutoffFactor_norm_pos {v : BondVector} (h : ‖v‖ < ρ) : 0 < cutoffFactor ρ p ‖v‖ := by
  unfold cutoffFactor
  rw [if_pos h]
  exact Real.exp_pos _
theorem hasDerivAt_levelCutoff_line (hρ : 0 < ρ) (hp : IsCutoff ρ p) {v : BondVector} (hv : ‖v‖ < ρ)
    (e : BondVector) {ε : ℝ} :
    HasDerivAt (fun τ : ℝ => levelCutoff ρ p ε (v + τ • e))
      (deriv smoothStep (cutoffFactor ρ p ‖v‖ / ε) *
        (-(cutoffFactor ρ p ‖v‖ * radialCutoffSlope p v e) / ε)) 0 := by
  have h1 := (hasDerivAt_cutoffFactor_line hρ hp hv e).div_const ε
  have h2 : HasDerivAt smoothStep (deriv smoothStep (cutoffFactor ρ p ‖v + (0 : ℝ) • e‖ / ε))
      (cutoffFactor ρ p ‖v + (0 : ℝ) • e‖ / ε) :=
    ((contDiff_smoothStep.differentiable (by norm_num)) _).hasDerivAt
  have h3 := h2.comp (0 : ℝ) h1
  simpa [levelCutoff, Function.comp_def] using h3
def levelCutoffProd (ρ : ℝ) (p : ℝ → ℝ) (ε : ℝ) (η : BondField ι) : ℝ :=
  ∏ b, levelCutoff ρ p ε (η b)
theorem contDiff_levelCutoffProd (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (ε : ℝ) : ContDiff ℝ 1 (levelCutoffProd (ι := ι) ρ p ε) := by
  have hs : ∀ s : Finset ι, ContDiff ℝ 1 (fun η : BondField ι => ∏ b ∈ s, levelCutoff ρ p ε (η b)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using contDiff_const
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact ((contDiff_levelCutoff hR hρ hp ε).comp (contDiff_apply ℝ BondVector a)).mul ih
  exact hs Finset.univ
theorem abs_levelCutoffProd_le_one (ε : ℝ) (η : BondField ι) : |levelCutoffProd ρ p ε η| ≤ 1 := by
  unfold levelCutoffProd
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun b _ => abs_nonneg _) (fun b _ => abs_smoothStep_le_one _)
def levelCutoffProdErase (ρ : ℝ) (p : ℝ → ℝ) (ε : ℝ) (b : ι) (η : BondField ι) : ℝ :=
  ∏ c ∈ Finset.univ.erase b, levelCutoff ρ p ε (η c)
theorem abs_levelCutoffProdErase_le_one (ε : ℝ) (b : ι) (η : BondField ι) :
    |levelCutoffProdErase ρ p ε b η| ≤ 1 := by
  unfold levelCutoffProdErase
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun b _ => abs_nonneg _) (fun b _ => abs_smoothStep_le_one _)
theorem levelCutoffProd_eq_mul (ε : ℝ) (b : ι) (η : BondField ι) :
    levelCutoffProd ρ p ε η = levelCutoff ρ p ε (η b) * levelCutoffProdErase ρ p ε b η := by
  unfold levelCutoffProd levelCutoffProdErase
  exact (Finset.mul_prod_erase Finset.univ (fun c => levelCutoff ρ p ε (η c)) (Finset.mem_univ b)).symm
theorem hasDerivAt_levelCutoffProd_line (hρ : 0 < ρ) (hp : IsCutoff ρ p) {η : BondField ι}
    (hη : ∀ c, ‖η c‖ < ρ) (b : ι) (e : BondVector) (ε : ℝ) :
    HasDerivAt (fun τ : ℝ => levelCutoffProd ρ p ε (η + τ • bondVariation b e))
      (deriv smoothStep (cutoffFactor ρ p ‖η b‖ / ε) *
        (-(cutoffFactor ρ p ‖η b‖ * radialCutoffSlope p (η b) e) / ε) *
        levelCutoffProdErase ρ p ε b η) 0 := by
  have e1 : (fun τ : ℝ => levelCutoffProd ρ p ε (η + τ • bondVariation b e)) =
      fun τ => levelCutoff ρ p ε (η b + τ • e) * levelCutoffProdErase ρ p ε b η := by
    funext τ
    rw [levelCutoffProd_eq_mul ε b, add_smul_bondVariation_apply, if_pos rfl]
    congr 1
    unfold levelCutoffProdErase
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [add_smul_bondVariation_apply, if_neg (Finset.ne_of_mem_erase hc)]
  rw [e1]
  exact (hasDerivAt_levelCutoff_line hρ hp (hη b) e).mul_const _
theorem contDiff_ballDensity (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    {Ψ : BondField ι → ℝ} (hΨ : ContDiff ℝ 1 Ψ) :
    ContDiff ℝ 1 (ballDensity (cutoffFactor ρ p) Ψ) := by
  have hf := contDiff_cutoffFactor_norm hR hρ hp
  have hs : ∀ s : Finset ι, ContDiff ℝ 1
      (fun η : BondField ι => ∏ b ∈ s, cutoffFactor ρ p ‖η b‖) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using contDiff_const
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hf.comp (contDiff_apply ℝ BondVector a)).mul ih
  exact (hs Finset.univ).mul hΨ.neg.exp
end AlongField
open AlongField in
theorem integrationByPartsAlongField (hby : IntegralByPartsAtBond) (hR : CutoffFactorIsRadialCutoff) :
    integrationByPartsAlongFieldStatement := by
  intro ι _ _ ρ p Ψ G b z C hρ hp hΨ hG hz hzC hdC hA hS hT
  set W := ballDensity (cutoffFactor ρ p) Ψ with hW
  have hWs : ContDiff ℝ 1 W := contDiff_ballDensity hR hρ hp hΨ
  have hopen : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by
    have : {η : BondField ι | ∀ b, ‖η b‖ < ρ} = ⋂ b, {η | ‖η b‖ < ρ} := by
      ext η
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun b =>
      isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  have hW0 : ∀ η : BondField ι, ¬ (∀ c, ‖η c‖ < ρ) → W η = 0 := by
    intro η hη
    obtain ⟨c, hc⟩ := not_forall.1 hη
    have : radialWeightProd (cutoffFactor ρ p) η = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ c) (cutoffFactor_norm_of_le (not_lt.1 hc))
    simp [hW, ballDensity, this]
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hεp : ∀ n, 0 < ε n := fun n => by
    simp only [hε]
    positivity
  set u : ℕ → BondField ι → ℝ := fun n η => G η * W η * levelCutoffProd ρ p (ε n) η with hu
  have hfc : ∀ c : ι, Continuous fun η : BondField ι => cutoffFactor ρ p ‖η c‖ := fun c =>
    (contDiff_cutoffFactor_norm hR hρ hp).continuous.comp (continuous_apply c)
  have near0 : ∀ n (η : BondField ι), ¬ (∀ c, ε n ≤ cutoffFactor ρ p ‖η c‖) →
      u n =ᶠ[nhds η] fun _ => 0 := by
    intro n η hη
    obtain ⟨c, hc⟩ := not_forall.1 hη
    have hlt := not_le.1 hc
    filter_upwards [(hfc c).continuousAt.eventually_lt continuousAt_const hlt] with ζ hζ
    have : levelCutoffProd ρ p (ε n) ζ = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
      unfold levelCutoff
      apply smoothStep_of_le_one
      rw [div_le_one (hεp n)]
      exact hζ.le
    simp only [hu, this, mul_zero]
  have inBalls : ∀ n (η : BondField ι), (∀ c, ε n ≤ cutoffFactor ρ p ‖η c‖) → ∀ c, ‖η c‖ < ρ := by
    intro n η hη c
    by_contra h
    have := hη c
    rw [cutoffFactor_norm_of_le (not_lt.1 h)] at this
    exact absurd (hεp n) (not_lt.2 this)
  have hus : ∀ n, ContDiff ℝ 1 (u n) := by
    intro n
    rw [contDiff_iff_contDiffAt]
    intro η
    by_cases h : ∀ c, ε n ≤ cutoffFactor ρ p ‖η c‖
    · have hη := inBalls n η h
      have hGa : ContDiffAt ℝ 1 G η := hG.contDiffAt (hopen.mem_nhds hη)
      exact (hGa.mul hWs.contDiffAt).mul (contDiff_levelCutoffProd hR hρ hp (ε n)).contDiffAt
    · exact contDiffAt_const.congr_of_eventuallyEq (near0 n η h)
  have hcs : ∀ n, HasCompactSupport (u n) := by
    intro n
    refine HasCompactSupport.intro (isCompact_closedBall (0 : BondField ι) ρ) fun η hη => ?_
    have : ¬ (∀ c, ‖η c‖ < ρ) := by
      intro h
      apply hη
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg hρ.le).2 fun c => (h c).le
    simp [hu, hW0 η this]
  have key : ∀ n, ∫ η, (fderiv ℝ (u n) η (bondVariation b (z (η b))) +
      bondDivergence z (η b) * u n η) = 0 := by
    intro n
    refine hby ι b z (u n) C hz hzC hdC ((hus n).differentiable (by norm_num))
      ((hus n).continuous.integrable_of_hasCompactSupport (hcs n)) fun e => ?_
    exact (((hus n).continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hcs n).fderiv_apply ℝ _)
  set tail : ℕ → BondField ι → ℝ := fun n η => G η * W η *
    (deriv smoothStep (cutoffFactor ρ p ‖η b‖ / ε n) *
      (-(cutoffFactor ρ p ‖η b‖ * radialCutoffSlope p (η b) (z (η b))) / ε n) *
      levelCutoffProdErase ρ p (ε n) b η) with htail
  set main : BondField ι → ℝ := fun η =>
    fieldDerivative b z G η * W η - G η * fieldScore p Ψ b z η * W η with hmain
  have hpt : ∀ n (η : BondField ι), (∀ c, ‖η c‖ < ρ) →
      fderiv ℝ (u n) η (bondVariation b (z (η b))) + bondDivergence z (η b) * u n η =
        levelCutoffProd ρ p (ε n) η * main η + tail n η := by
    intro n η hη
    set e := z (η b) with he
    have hGd : DifferentiableAt ℝ G η :=
      (hG.contDiffAt (hopen.mem_nhds hη)).differentiableAt (by norm_num)
    have hΨd : DifferentiableAt ℝ Ψ η := (hΨ.differentiable (by norm_num)) η
    have hl : HasDerivAt (fun τ : ℝ => η + τ • bondVariation b e) (bondVariation b e) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (bondVariation b e)).const_add η
    have hGl : HasDerivAt (fun τ : ℝ => G (η + τ • bondVariation b e))
        (fderiv ℝ G η (bondVariation b e)) 0 := by
      have h2 : HasFDerivAt G (fderiv ℝ G η) (η + (0 : ℝ) • bondVariation b e) := by
        simpa using hGd.hasFDerivAt
      exact h2.comp_hasDerivAt (0 : ℝ) hl
    have hul : HasDerivAt (fun τ : ℝ => u n (η + τ • bondVariation b e))
        (fderiv ℝ (u n) η (bondVariation b e)) 0 := by
      have h2 : HasFDerivAt (u n) (fderiv ℝ (u n) η) (η + (0 : ℝ) • bondVariation b e) := by
        simpa using (((hus n).differentiable (by norm_num)) η).hasFDerivAt
      exact h2.comp_hasDerivAt (0 : ℝ) hl
    have hprod := (hGl.mul (hasDerivAt_ballDensity_line hρ hp hη hΨd b e)).mul
      (hasDerivAt_levelCutoffProd_line hρ hp hη b e (ε n))
    have e0 : G (η + (0 : ℝ) • bondVariation b e) = G η := by simp
    have e1 : ballDensity (cutoffFactor ρ p) Ψ (η + (0 : ℝ) • bondVariation b e) = W η := by simp [hW]
    have e2 : levelCutoffProd ρ p (ε n) (η + (0 : ℝ) • bondVariation b e) =
        levelCutoffProd ρ p (ε n) η := by simp
    have eW : ballDensity (cutoffFactor ρ p) Ψ η = W η := rfl
    simp only [Pi.mul_apply, e0, e1, e2, eW] at hprod
    have hd := hul.unique hprod
    rw [hd]
    simp only [hu, hmain, htail, fieldDerivative, fieldScore, bondPartialDeriv, ← he]
    ring
  have hzero : ∀ n (η : BondField ι), ¬ (∀ c, ‖η c‖ < ρ) →
      fderiv ℝ (u n) η (bondVariation b (z (η b))) + bondDivergence z (η b) * u n η = 0 := by
    intro n η hη
    have h1 : ¬ (∀ c, ε n ≤ cutoffFactor ρ p ‖η c‖) := fun h => hη (inBalls n η h)
    have h2 := (near0 n η h1)
    have h3 : fderiv ℝ (u n) η = 0 := by
      rw [h2.fderiv_eq]
      simp
    have h4 : u n η = 0 := h2.self_of_nhds
    simp [h3, h4]
  obtain ⟨Kd, hKd0, hKd⟩ := exists_abs_deriv_smoothStep_le
  have hT' : Integrable fun η => G η * radialCutoffSlope p (η b) (z (η b)) * W η := hT
  have hM : Integrable main := hA.sub hS
  set dom : BondField ι → ℝ := fun η => |main η| +
    2 * Kd * |G η * radialCutoffSlope p (η b) (z (η b)) * W η| with hdom
  have hdomI : Integrable dom := hM.abs.add (hT'.abs.const_mul _)
  have hzc : Continuous z := hz.continuous
  have hdc : Continuous (fderiv ℝ z) := hz.continuous_fderiv (by norm_num)
  have hpr : Continuous fun η : BondField ι => η b := continuous_apply b
  have hdiv : Continuous fun η : BondField ι => bondDivergence z (η b) := by
    unfold bondDivergence
    refine continuous_finset_sum _ fun i _ => ?_
    exact (EuclideanSpace.proj i : BondVector →L[ℝ] ℝ).continuous.comp
      ((hdc.comp hpr).clm_apply continuous_const)
  have hat : Continuous fun η : BondField ι => bondVariation b (z (η b)) := by
    have e : (fun η : BondField ι => bondVariation b (z (η b))) =
        fun η => ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b (z (η b)) := by
      funext η
      rfl
    rw [e]
    exact (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b).continuous.comp (hzc.comp hpr)
  have hlim := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (BondField ι)))
    (F := fun n η => fderiv ℝ (u n) η (bondVariation b (z (η b))) + bondDivergence z (η b) * u n η)
    (f := main) dom
    (fun n => ((((hus n).continuous_fderiv (by norm_num)).clm_apply hat).add
      (hdiv.mul (hus n).continuous)).aestronglyMeasurable) hdomI
    (fun n => Filter.Eventually.of_forall fun η => ?_)
    (Filter.Eventually.of_forall fun η => ?_)
  · have h0 : ∫ η, main η = 0 := by
      have hc : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds (∫ η, main η)) := by
        refine hlim.congr fun n => key n
      exact (tendsto_nhds_unique hc tendsto_const_nhds)
    simp only [hmain] at h0
    rw [integral_sub hA hS] at h0
    linarith
  · by_cases hη : ∀ c, ‖η c‖ < ρ
    · rw [hpt n η hη, Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        have := abs_levelCutoffProd_le_one (ρ := ρ) (p := p) (ε n) η
        nlinarith [abs_nonneg (main η)]
      · simp only [htail]
        set s₀ := cutoffFactor ρ p ‖η b‖ with hs₀
        set t₀ := s₀ / ε n with ht₀
        have hs0 : 0 ≤ s₀ := (cutoffFactor_norm_pos (hη b)).le
        have ht0 : 0 ≤ t₀ := div_nonneg hs0 (hεp n).le
        set rr := radialCutoffSlope p (η b) (z (η b)) with hrr
        have e1 : deriv smoothStep t₀ * (-(s₀ * rr) / ε n) = -(deriv smoothStep t₀ * t₀) * rr := by
          simp only [ht₀]
          ring
        have h1 : |deriv smoothStep t₀ * t₀| ≤ 2 * Kd := by
          by_cases h2 : t₀ ≤ 2
          · rw [abs_mul, abs_of_nonneg ht0]
            nlinarith [hKd t₀, abs_nonneg (deriv smoothStep t₀)]
          · rw [deriv_smoothStep_of_lt_or_gt (Or.inr (not_le.1 h2))]
            simp
            linarith
        rw [e1]
        have h3 := abs_levelCutoffProdErase_le_one (ρ := ρ) (p := p) (ε n) b η
        have e2 : G η * W η * (-(deriv smoothStep t₀ * t₀) * rr * levelCutoffProdErase ρ p (ε n) b η) =
            (G η * rr * W η) * (-(deriv smoothStep t₀ * t₀) * levelCutoffProdErase ρ p (ε n) b η) := by
          ring
        have h4 : |deriv smoothStep t₀ * t₀| * |levelCutoffProdErase ρ p (ε n) b η| ≤ 2 * Kd := by
          nlinarith [abs_nonneg (deriv smoothStep t₀ * t₀), abs_nonneg (levelCutoffProdErase ρ p (ε n) b η)]
        have h5 : |-(deriv smoothStep t₀ * t₀) * levelCutoffProdErase ρ p (ε n) b η| ≤ 2 * Kd := by
          rw [abs_mul, abs_neg]
          exact h4
        rw [e2]
        calc |G η * rr * W η * (-(deriv smoothStep t₀ * t₀) * levelCutoffProdErase ρ p (ε n) b η)|
            = |G η * rr * W η| * |-(deriv smoothStep t₀ * t₀) * levelCutoffProdErase ρ p (ε n) b η| :=
              abs_mul _ _
          _ ≤ |G η * rr * W η| * (2 * Kd) := mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
          _ = 2 * Kd * |G η * rr * W η| := by ring
    · rw [hzero n η hη]
      simp only [norm_zero, hdom]
      positivity
  · by_cases hη : ∀ c, ‖η c‖ < ρ
    · have hev : ∀ᶠ n : ℕ in Filter.atTop, ∀ c, 2 * ε n < cutoffFactor ρ p ‖η c‖ := by
        rw [Filter.eventually_all]
        intro c
        have hε0 : Filter.Tendsto ε Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 : Filter.Tendsto (fun n => 2 * ε n) Filter.atTop (nhds 0) := by
          simpa using hε0.const_mul 2
        exact h2.eventually_lt tendsto_const_nhds (cutoffFactor_norm_pos (hη c))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      rw [hpt n η hη]
      have hc1 : levelCutoffProd ρ p (ε n) η = 1 := by
        unfold levelCutoffProd
        refine Finset.prod_eq_one fun c _ => ?_
        unfold levelCutoff
        apply smoothStep_of_two_le
        rw [le_div_iff₀ (hεp n)]
        exact (hn c).le
      have ht : tail n η = 0 := by
        simp only [htail]
        have h2 : 2 < cutoffFactor ρ p ‖η b‖ / ε n := by
          rw [lt_div_iff₀ (hεp n)]
          exact hn b
        rw [deriv_smoothStep_of_lt_or_gt (Or.inr h2)]
        simp
      rw [hc1, ht]
      ring
    · have h0 : main η = 0 := by
        simp [hmain, hW0 η hη]
      rw [h0]
      refine tendsto_const_nhds.congr fun n => ?_
      exact (hzero n η hη).symm
end YangMills.Construction.BondIntegration
end
