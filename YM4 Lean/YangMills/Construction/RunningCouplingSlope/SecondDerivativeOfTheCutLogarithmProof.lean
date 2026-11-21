import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACut
import YangMills.Construction.ColdStepAtMirrorFrames.SmoothNearACompactSet
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeOfTheCutLogarithm
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open YangMills.Construction.ColdStepAtMirrorFrames
open scoped Topology
namespace YangMills.Construction.LaplaceAsymptotics
private theorem iteratedFDeriv_two_comp_scalar {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ ψ : ℝ → ℝ) (c : ℝ) (f : E → ℝ) (z : E) (hf : ContDiffAt ℝ 2 f z)
    (hφ : ∀ᶠ y in 𝓝 (f z), HasDerivAt φ (ψ y) y) (hψ : HasDerivAt ψ c (f z)) (v : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (fun y => φ (f y)) z v =
      ψ (f z) * iteratedFDeriv ℝ 2 f z v + c * (fderiv ℝ f z (v 0) * fderiv ℝ f z (v 1)) := by
  have hdiff : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hcont : ContinuousAt f z := hf.continuousAt
  have heq : fderiv ℝ (fun y => φ (f y)) =ᶠ[𝓝 z] fun y => ψ (f y) • fderiv ℝ f y := by
    filter_upwards [hdiff, Filter.Tendsto.eventually hcont hφ] with y hy hy'
    exact (hy'.comp_hasFDerivAt y hy.hasFDerivAt).fderiv
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hF : HasFDerivAt (fun y => ψ (f y)) (c • fderiv ℝ f z) z :=
    hψ.comp_hasFDerivAt z (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hS : HasFDerivAt (fun y => ψ (f y) • fderiv ℝ f y) _ z := hF.smul hD
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, heq.fderiv_eq, hS.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring
private theorem fderiv_prod_slice {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E × F → ℝ) (η : F) (τ : E)
    (h : DifferentiableAt ℝ A (τ, η)) :
    fderiv ℝ (fun t => A (t, η)) τ = (fderiv ℝ A (τ, η)).comp (ContinuousLinearMap.inl ℝ E F) := by
  have hι : HasFDerivAt (fun t : E => (t, η)) (ContinuousLinearMap.inl ℝ E F) τ :=
    (hasFDerivAt_id τ).prodMk (hasFDerivAt_const η τ)
  exact (HasFDerivAt.comp τ h.hasFDerivAt hι).fderiv
private theorem iteratedFDeriv_two_prod_slice {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E × F → ℝ) (η : F)
    (hA : ContDiffAt ℝ 2 A ((0 : E), η)) (v : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (fun t => A (t, η)) 0 v =
      iteratedFDeriv ℝ 2 A (0, η) fun i => (v i, 0) := by
  have hι : HasFDerivAt (fun t : E => (t, η)) (ContinuousLinearMap.inl ℝ E F) (0 : E) :=
    (hasFDerivAt_id (0 : E)).prodMk (hasFDerivAt_const η (0 : E))
  have hdiff : ∀ᶠ t in 𝓝 (0 : E), DifferentiableAt ℝ A (t, η) := by
    filter_upwards [Filter.Tendsto.eventually hι.continuousAt (hA.eventually (by simp))] with t ht
    exact ht.differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun t => A (t, η)) =ᶠ[𝓝 (0 : E)]
      fun t => (fderiv ℝ A (t, η)).comp (ContinuousLinearMap.inl ℝ E F) := by
    filter_upwards [hdiff] with t ht using fderiv_prod_slice A η t ht
  have hD : HasFDerivAt (fderiv ℝ A) (fderiv ℝ (fderiv ℝ A) ((0 : E), η)) ((0 : E), η) :=
    ((hA.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  set T : ((E × F) →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ E (E × F) ℝ).flip (ContinuousLinearMap.inl ℝ E F) with hT
  have hC : HasFDerivAt (fun t => T (fderiv ℝ A (t, η)))
      (T.comp ((fderiv ℝ (fderiv ℝ A) ((0 : E), η)).comp (ContinuousLinearMap.inl ℝ E F))) (0 : E) :=
    T.hasFDerivAt.comp (0 : E) (HasFDerivAt.comp (0 : E) hD hι)
  have e : (fun t => (fderiv ℝ A (t, η)).comp (ContinuousLinearMap.inl ℝ E F)) =
      fun t => T (fderiv ℝ A (t, η)) := rfl
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, heq.fderiv_eq, e, hC.fderiv]
  rfl
theorem logCutoffIntegralSecondDeriv_holds (hR : CutoffFactorIsRadialCutoff)
    (hT : UniformDerivBoundNearCompactOfContinuous) (hW : GibbsMeanDifferentiation) :
    logCutoffIntegralSecondDeriv := by
  intro ι _ _ ρ x p Q B hρ hp hQ hB
  have hr := hR ρ p hρ hp
  set r : ℝ → ℝ := fun u => cutoffFactor ρ p (max u 0) with hrdef
  have hrad : ∀ η : BondField ι, radialWeightProd (cutoffFactor ρ p) η = radialWeightProd r η := by
    intro η
    unfold radialWeightProd
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [hrdef, max_eq_left (norm_nonneg (η b))]
  have hrc : Continuous r := hr.smooth.continuous
  have hRc : Continuous (fun η : BondField ι => radialWeightProd r η) := by
    unfold radialWeightProd
    exact continuous_finsetProd _ fun b _ => hrc.comp (continuous_norm.comp (continuous_apply b))
  set K : Set (BondField ι) := {η | ∀ b, ‖η b‖ ≤ ρ} with hK
  have hcomp : IsCompact K := by
    have : K = Set.pi Set.univ fun _ => Metric.closedBall 0 ρ := by
      ext η
      simp [hK]
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hm : MeasurableSet K := hcomp.isClosed.measurableSet
  set E : (Fin 2 → ℝ) × BondField ι → ℝ := fun z => Real.exp (-(x * Q z + B z)) with hE
  have hEs : ∀ η ∈ K, ContDiffAt ℝ 3 E (0, η) := fun η hη =>
    ((contDiffAt_const.mul (hQ η hη)).add (hB η hη)).neg.exp
  obtain ⟨s, M, hs, hcont, hsm⟩ := hT 2 (BondField ι) E K hcomp hEs
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hRc.continuousOn
  set μ : Measure (BondField ι) := volume.restrict K with hμ
  have : IsFiniteMeasure μ := ⟨by
    rw [hμ, Measure.restrict_apply_univ]
    exact hcomp.measure_lt_top⟩
  set G : (Fin 2 → ℝ) → BondField ι → ℝ := fun τ η => radialWeightProd r η * E (τ, η) with hG
  have hopen : IsOpen (Metric.ball (0 : Fin 2 → ℝ) s) := Metric.isOpen_ball
  have hGc : ∀ τ ∈ Metric.ball (0 : Fin 2 → ℝ) s, ContinuousOn (G τ) K := fun τ hτ =>
    hRc.continuousOn.mul (hcont τ hτ)
  have hdom : IsDominatedSmoothFamily μ 3 (Metric.ball (0 : Fin 2 → ℝ) s) (|C| * |M|) G := by
    refine ⟨fun τ hτ => (hGc τ hτ).aestronglyMeasurable hm, ?_, ?_⟩
    · refine ae_restrict_of_forall_mem hm fun η hη => ?_
      exact contDiffOn_const.mul (hsm η hη).1
    · refine ae_restrict_of_forall_mem hm fun η hη j hj τ hτ => ?_
      have hat : ContDiffAt ℝ j (fun τ => E (τ, η)) τ :=
        (((hsm η hη).1.of_le (by exact_mod_cast hj)).contDiffAt (hopen.mem_nhds hτ))
      have e : (fun τ => G τ η) = radialWeightProd r η • fun τ => E (τ, η) := by
        funext τ
        simp [hG]
      rw [e, iteratedFDeriv_const_smul_apply hat, norm_smul]
      have h1 : ‖radialWeightProd r η‖ ≤ |C| := (hC η hη).trans (le_abs_self C)
      have h2 : ‖iteratedFDeriv ℝ j (fun τ => E (τ, η)) τ‖ ≤ |M| :=
        ((hsm η hη).2 j hj τ hτ).trans (le_abs_self M)
      exact mul_le_mul h1 h2 (norm_nonneg _) (abs_nonneg _)
  have hI := hW.1 (BondField ι) μ 2 3 _ _ G hopen hdom
  have h0 : (0 : Fin 2 → ℝ) ∈ Metric.ball (0 : Fin 2 → ℝ) s := Metric.mem_ball_self hs
  set F : (Fin 2 → ℝ) → ℝ := fun τ => ∫ η, G τ η ∂μ with hFdef
  have hF2 : ContDiffAt ℝ 2 F 0 :=
    (hI.1.contDiffAt (Metric.ball_mem_nhds _ hs)).of_le (by norm_num)
  have hnn : ∀ η : BondField ι, 0 ≤ radialWeightProd r η := fun η =>
    Finset.prod_nonneg fun b _ => by
      rcases lt_or_ge ‖η b‖ ρ with h | h
      · exact (hr.pos _ (norm_nonneg _) h).le
      · exact (hr.zero _ h).ge
  have hint : Integrable (G 0) μ := by
    refine Integrable.of_bound ((hGc 0 h0).aestronglyMeasurable hm) (|C| * |M|) ?_
    filter_upwards [hdom.norm_iteratedFDeriv_le] with η hη
    have := hη 0 (by norm_num) 0 h0
    simpa using this
  have hpos : 0 < F 0 := by
    show 0 < ∫ η, G 0 η ∂μ
    rw [hμ, setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun η => mul_nonneg (hnn η) (Real.exp_pos _).le) hint]
    have hsub : Metric.ball (0 : BondField ι) ρ ⊆ Function.support (G 0) ∩ K := by
      intro η hη
      have hlt : ∀ b, ‖η b‖ < ρ := fun b =>
        (norm_le_pi_norm η b).trans_lt (mem_ball_zero_iff.mp hη)
      refine ⟨?_, fun b => (hlt b).le⟩
      have : 0 < radialWeightProd r η := Finset.prod_pos fun b _ => hr.pos _ (norm_nonneg _) (hlt b)
      exact (mul_pos this (Real.exp_pos _)).ne'
    exact (Metric.measure_ball_pos volume 0 hρ).trans_le (measure_mono hsub)
  have hzero : ∀ η, η ∉ K → radialWeightProd r η = 0 := by
    intro η hη
    simp only [hK, Set.mem_ofPred_eq, not_forall, not_le] at hη
    obtain ⟨b, hb⟩ := hη
    exact Finset.prod_eq_zero (Finset.mem_univ b) (hr.zero _ hb.le)
  have e : logCutoffIntegral ρ p x Q B = fun τ => Real.log (F τ) := by
    funext τ
    unfold logCutoffIntegral
    congr 1
    show _ = ∫ η, G τ η ∂μ
    rw [hμ, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
      simp only [hG, hE, hrad η]
    · intro η hη
      simp [hG, hzero η hη]
  set A := linearExponent x Q B with hAdef
  set v : Fin 2 → Fin 2 → ℝ := fun l => Pi.single l 1 with hvdef
  set f0 := rimWeightedDensity ρ p x Q B with hf0
  have hf0G : ∀ η, f0 η = G 0 η := fun η => by
    show radialWeightProd (cutoffFactor ρ p) η * _ = radialWeightProd r η * _
    rw [hrad η]
  have hf0z : ∀ η, η ∉ K → f0 η = 0 := fun η hη => by
    rw [hf0G]
    simp [hG, hzero η hη]
  have hA3 : ∀ η ∈ K, ContDiffAt ℝ 3 A (0, η) := fun η hη =>
    (contDiffAt_const.mul (hQ η hη)).add (hB η hη)
  have hpt : ∀ η ∈ K,
      (∀ l, iteratedFDeriv ℝ 1 (fun τ => G τ η) 0 ![v l] =
        -(parameterSlope A l η * f0 η)) ∧
      iteratedFDeriv ℝ 2 (fun τ => G τ η) 0 v =
        (-parameterMixedDeriv A η + parameterSlope A 0 η * parameterSlope A 1 η) * f0 η := by
    intro η hη
    have hA2 : ContDiffAt ℝ 2 A (0, η) := (hA3 η hη).of_le (by norm_num)
    have ha : ContDiffAt ℝ 2 (fun t : Fin 2 → ℝ => A (t, η)) 0 :=
      ContDiffAt.comp (f := fun t : Fin 2 → ℝ => (t, η)) (0 : Fin 2 → ℝ) hA2 (by fun_prop)
    obtain ⟨R, hRdef⟩ : ∃ R, R = radialWeightProd r η := ⟨_, rfl⟩
    have hφ : ∀ y : ℝ, HasDerivAt (fun y => R * Real.exp (-y)) (-(R * Real.exp (-y))) y := fun y => by
      have := ((hasDerivAt_neg y).exp).const_mul R
      exact this.congr_deriv (by ring)
    have hψ : HasDerivAt (fun y => -(R * Real.exp (-y))) (R * Real.exp (-(A (0, η)))) (A (0, η)) :=
      (hφ (A (0, η))).fun_neg.congr_deriv (neg_neg _)
    have hGe : (fun τ => G τ η) = fun τ => R * Real.exp (-(A (τ, η))) := by
      rw [hRdef]
      rfl
    have hf0e : f0 η = R * Real.exp (-(A (0, η))) := by
      rw [hf0G, hRdef]
      rfl
    have hsl : ∀ l, fderiv ℝ (fun t : Fin 2 → ℝ => A (t, η)) 0 (v l) =
        parameterSlope A l η := fun l => by
      rw [fderiv_prod_slice A η 0 (hA2.differentiableAt (by norm_num))]
      rfl
    have hmx : iteratedFDeriv ℝ 2 (fun t : Fin 2 → ℝ => A (t, η)) 0 v = parameterMixedDeriv A η :=
      iteratedFDeriv_two_prod_slice A η hA2 v
    constructor
    · intro l
      rw [iteratedFDeriv_one_apply, hGe]
      have h1 := ((hφ (A (0, η))).comp_hasFDerivAt (0 : Fin 2 → ℝ)
        (ha.differentiableAt (by norm_num)).hasFDerivAt).fderiv
      have h2 : fderiv ℝ (fun τ => R * Real.exp (-(A (τ, η)))) 0 =
          -(R * Real.exp (-(A (0, η)))) • fderiv ℝ (fun t : Fin 2 → ℝ => A (t, η)) 0 := h1
      rw [h2]
      simp only [Matrix.cons_val_zero, smul_apply, smul_eq_mul, hsl, hf0e]
      ring
    · rw [hGe]
      have h := iteratedFDeriv_two_comp_scalar (fun y => R * Real.exp (-y)) (fun y => -(R * Real.exp (-y)))
        (R * Real.exp (-(A (0, η)))) (fun t : Fin 2 → ℝ => A (t, η)) 0 ha
        (Filter.Eventually.of_forall hφ) hψ v
      rw [h, hmx, hsl, hsl, hf0e]
      ring
  have htoV : ∀ g : BondField ι → ℝ, ∫ η, g η * f0 η = ∫ η, g η * f0 η ∂μ := fun g => by
    rw [hμ, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro η hη
    simp [hf0z η hη]
  have hZ : ∫ η, f0 η = F 0 := by
    have h1 : ∫ η, f0 η = ∫ η, f0 η ∂μ := by
      rw [hμ, setIntegral_eq_integral_of_forall_compl_eq_zero]
      exact hf0z
    rw [h1]
    exact integral_congr_ae (Filter.Eventually.of_forall hf0G)
  have hD1 : ∀ l, fderiv ℝ F 0 (v l) = -∫ η, parameterSlope A l η * f0 η := fun l => by
    have h := hI.2 0 h0 1 (by norm_num) ![v l]
    rw [iteratedFDeriv_one_apply] at h
    rw [htoV, ← integral_neg]
    refine h.trans (integral_congr_ae (ae_restrict_of_forall_mem hm fun η hη => ?_))
    exact (hpt η hη).1 l
  have hD2 : iteratedFDeriv ℝ 2 F 0 v =
      ∫ η, (-parameterMixedDeriv A η +
        parameterSlope A 0 η * parameterSlope A 1 η) * f0 η := by
    have h := hI.2 0 h0 2 (by norm_num) v
    rw [htoV]
    refine h.trans (integral_congr_ae (ae_restrict_of_forall_mem hm fun η hη => ?_))
    exact (hpt η hη).2
  have hne : F 0 ≠ 0 := hpos.ne'
  have hlog := iteratedFDeriv_two_comp_scalar Real.log (fun y => y⁻¹) (-(F 0 ^ 2)⁻¹) F 0 hF2
    (Filter.Eventually.mono (isOpen_ne.mem_nhds hne) fun y hy => Real.hasDerivAt_log hy) (hasDerivAt_inv hne) v
  rw [e, hlog, hD2]
  rw [hD1 0, hD1 1]
  unfold densityMean
  rw [hZ]
  field_simp
  ring
end YangMills.Construction.LaplaceAsymptotics
end
