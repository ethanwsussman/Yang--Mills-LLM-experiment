import YangMills.Construction.ClusterExpansionOfAStep.FourConvexPotentials
import YangMills.Construction.ClusterExpansionOfAStep.LawsOnProductsOfBalls
import YangMills.Construction.ClusterExpansionOfAStep.MixedDifferenceOfALogarithm
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ConvexPotentials
open ColdStepAtMirrorFrames MixedDifferences ConvexMeasures
section LinearCombinations
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem fderiv_linComb {f g : BondField ι → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (a c : ℝ)
    (x : BondField ι) :
    fderiv ℝ (fun y => a * f y + c * g y) x = a • fderiv ℝ f x + c • fderiv ℝ g x := by
  have hsum : HasFDerivAt (fun y => a * f y + c * g y) (a • fderiv ℝ f x + c • fderiv ℝ g x) x :=
    ((hf x).hasFDerivAt.const_mul a).add ((hg x).hasFDerivAt.const_mul c)
  exact hsum.fderiv
theorem isUniformlyConvexDecaying_convexComb {ρ m κ : ℝ} {d : ι → ι → ℝ} {Φ Φ' : BondField ι → ℝ}
    {K K' : ι → ι → ℝ} (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hΦ : IsUniformlyConvexDecaying ρ m κ d Φ K) (hΦ' : IsUniformlyConvexDecaying ρ m κ d Φ' K') :
    IsUniformlyConvexDecaying ρ m κ d (fun x => (1 - t) * Φ x + t * Φ' x)
      (fun b b' => (1 - t) * K b b' + t * K' b b') := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.isUniformlyConvexDecaying_convexComb <;> assumption
theorem bondGradNorm_linComb_le {f g : BondField ι → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (b : ι) (x : BondField ι) :
    bondGradNorm (fun y => a * f y + c * g y) b x ≤ a * bondGradNorm f b x + c * bondGradNorm g b x := by
  unfold bondGradNorm
  rw [fderiv_linComb hf hg, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.smul_comp]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hc]
end LinearCombinations
theorem fourCornerLogRatioBound_of_bounds (hcov : covarianceSupNormBound)
    (hmix : LogIntegralMixedDifferenceBound) (hrim : CutoffFactorIsRadialCutoff) :
    FourCornerLogRatioBound := by
  intro ι _ _ ρ m κ d Ψ K p Bf Bg Bc M hρ hm hκ hp hd hconv hbound hBf hBg hBc
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbound 0 0 0 (fun b => by simpa using hρ))
  have hΨc : ∀ i j, Continuous (Ψ i j) := fun i j => (hconv i j).smooth.continuous
  have hΨd : ∀ i j, Differentiable ℝ (Ψ i j) := fun i j => (hconv i j).smooth.differentiable (by norm_num)
  set r : ℝ → ℝ := cutoffFactor ρ p with hr
  have hRim := hrim ρ p hρ hp
  have hr_eq : ∀ η : BondField ι, ∀ b, r ‖η b‖ = cutoffFactor ρ p (max ‖η b‖ 0) := by
    intro η b
    rw [max_eq_left (norm_nonneg _)]
  set rim : BondField ι → ℝ := radialWeightProd r with hrimdef
  have hrim_cont : Continuous rim := by
    have : rim = fun η => ∏ b, cutoffFactor ρ p (max ‖η b‖ 0) := by
      funext η
      simp only [hrimdef, radialWeightProd]
      exact Finset.prod_congr rfl fun b _ => hr_eq η b
    rw [this]
    refine continuous_finset_prod _ fun b _ => ?_
    exact (hRim.smooth.continuous).comp (continuous_apply b).norm
  have hr_nonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ r u := by
    intro u hu
    by_cases h : u < ρ
    · have := hRim.pos u hu h
      simp only [max_eq_left hu] at this
      exact this.le
    · have := hRim.zero u (not_lt.mp h)
      simp only [max_eq_left hu] at this
      simp only [hr, this, le_refl]
  have hrim_nonneg : ∀ η, 0 ≤ rim η := fun η =>
    Finset.prod_nonneg fun b _ => hr_nonneg _ (norm_nonneg _)
  have hrim_zero : ∀ η : BondField ι, (¬ ∀ b, ‖η b‖ < ρ) → rim η = 0 := by
    intro η h
    push Not at h
    obtain ⟨b, hb⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
    have := hRim.zero _ hb
    rw [max_eq_left (norm_nonneg _)] at this
    exact this
  have hrim_one : rim 0 = 1 := by
    refine Finset.prod_eq_one fun b _ => ?_
    have := hRim.one 0 le_rfl (by positivity)
    simp only [max_self] at this
    simpa [hr] using this
  have hrim_comp : HasCompactSupport rim := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : BondField ι) ρ) fun η hη => ?_
    apply hrim_zero
    intro hall
    apply hη
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg hρ.le).mpr fun b => (hall b).le
  have hrim_int : Integrable rim (volume : Measure (BondField ι)) :=
    hrim_cont.integrable_of_hasCompactSupport hrim_comp
  set μ : Measure (BondField ι) := volume.withDensity fun η => ENNReal.ofReal (rim η) with hμ
  have hfin : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hrim_int.2
  have hconvert : ∀ G : BondField ι → ℝ, ∫ η, G η ∂μ = ∫ η, rim η * G η := by
    intro G
    have h1 : μ = volume.withDensity fun η => ((rim η).toNNReal : ENNReal) := rfl
    rw [h1, integral_withDensity_eq_integral_smul hrim_cont.measurable.real_toNNReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hrim_nonneg η)]
  have hdens_cont : ∀ E : BondField ι → ℝ, Continuous E → Continuous (ballDensity r E) := by
    intro E hE
    exact hrim_cont.mul (Real.continuous_exp.comp hE.neg)
  have hdens_comp : ∀ E : BondField ι → ℝ, HasCompactSupport (ballDensity r E) := by
    intro E
    exact hrim_comp.mul_right
  have hdens_nonneg : ∀ (E : BondField ι → ℝ) η, 0 ≤ ballDensity r E η := fun E η =>
    mul_nonneg (hrim_nonneg η) (Real.exp_pos _).le
  have hdens_int : ∀ E : BondField ι → ℝ, Continuous E →
      Integrable (ballDensity r E) (volume : Measure (BondField ι)) := fun E hE =>
    (hdens_cont E hE).integrable_of_hasCompactSupport (hdens_comp E)
  have hZpos : ∀ E : BondField ι → ℝ, Continuous E → 0 < cutoffIntegral ρ p E := by
    intro E hE
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) (hdens_cont E hE)
      (hdens_comp E) (hdens_nonneg E) ?_
    simp only [ballDensity]
    change rim 0 * _ ≠ 0
    rw [hrim_one]
    exact (mul_pos one_pos (Real.exp_pos _)).ne'
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h1 := hconvert (fun _ => 1)
    rw [h0] at h1
    simp only [integral_zero_measure, mul_one] at h1
    have h2 : 0 < ∫ η, rim η := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      hrim_cont hrim_comp hrim_nonneg (by rw [hrim_one]; exact one_ne_zero)
    linarith
  have hZeq : ∀ E E' : BondField ι → ℝ, (∀ η, (∀ b, ‖η b‖ < ρ) → E' η = E η) →
      ∫ η, Real.exp (-(E' η)) ∂μ = cutoffIntegral ρ p E := by
    intro E E' hE
    rw [hconvert]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [ballDensity]
    change rim η * _ = rim η * _
    by_cases hη : ∀ b, ‖η b‖ < ρ
    · rw [hE η hη]
    · rw [hrim_zero η hη]
      ring
  have hwm : ∀ E E' H H' : BondField ι → ℝ, (∀ η, (∀ b, ‖η b‖ < ρ) → E' η = E η) →
      (∀ η, (∀ b, ‖η b‖ < ρ) → H' η = H η) → gibbsMean μ E' H' = ballExpectation r E H := by
    intro E E' H H' hE hH
    simp only [gibbsMean, ballExpectation]
    rw [hconvert, hconvert]
    congr 1
    · refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
      simp only [ballDensity]
      change rim η * _ = _ * (rim η * _)
      by_cases hη : ∀ b, ‖η b‖ < ρ
      · rw [hE η hη, hH η hη]
        ring
      · rw [hrim_zero η hη]
        ring
    · refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
      simp only [ballDensity]
      change rim η * _ = rim η * _
      by_cases hη : ∀ b, ‖η b‖ < ρ
      · rw [hE η hη]
      · rw [hrim_zero η hη]
        ring
  set U : BondField ι → ℝ := Ψ 0 0 with hU
  set A : BondField ι → ℝ := fun η => Ψ 1 0 η - Ψ 0 0 η with hA
  set B : BondField ι → ℝ := fun η => Ψ 0 1 η - Ψ 0 0 η with hB
  set C : BondField ι → ℝ := fun η => Ψ 1 1 η - Ψ 1 0 η - Ψ 0 1 η + Ψ 0 0 η with hC
  have hsq : ∀ v w, bilinearExponent U A B C v w = fun η =>
      (1 - w) * ((1 - v) * Ψ 0 0 η + v * Ψ 1 0 η) + w * ((1 - v) * Ψ 0 1 η + v * Ψ 1 1 η) := by
    intro v w
    funext η
    simp only [bilinearExponent, hU, hA, hB, hC]
    ring
  have hmixconv : ∀ v w : ℝ, 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 →
      ∃ Kv, IsUniformlyConvexDecaying ρ m κ d (bilinearExponent U A B C v w) Kv := by
    intro v w h0 h1 h2 h3
    rw [hsq]
    exact ⟨_, isUniformlyConvexDecaying_convexComb w h2 h3
      (isUniformlyConvexDecaying_convexComb v h0 h1 (hconv 0 0) (hconv 1 0))
      (isUniformlyConvexDecaying_convexComb v h0 h1 (hconv 0 1) (hconv 1 1))⟩
  have hUc : Continuous U := hΨc 0 0
  have hAc : Continuous A := (hΨc 1 0).sub (hΨc 0 0)
  have hBc' : Continuous B := (hΨc 0 1).sub (hΨc 0 0)
  have hCc : Continuous C := (((hΨc 1 1).sub (hΨc 1 0)).sub (hΨc 0 1)).add (hΨc 0 0)
  have hopen : MeasurableSet {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by
    have : {η : BondField ι | ∀ b, ‖η b‖ < ρ} = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
      ext η
      simp
    rw [this]
    exact MeasurableSet.iInter fun b =>
      (isOpen_lt (continuous_apply b).norm continuous_const).measurableSet
  classical
  set cut : (BondField ι → ℝ) → BondField ι → ℝ :=
    fun f η => if ∀ b, ‖η b‖ < ρ then f η else 0 with hcut
  have hcut_meas : ∀ f : BondField ι → ℝ, Measurable f → Measurable (cut f) := by
    intro f hf
    exact Measurable.ite hopen hf measurable_const
  have hcut_in : ∀ (f : BondField ι → ℝ) η, (∀ b, ‖η b‖ < ρ) → cut f η = f η := by
    intro f η hη
    simp only [hcut, if_pos hη]
  have hcut_size : ∀ (f : BondField ι → ℝ) (G : ℝ), 0 ≤ G →
      (∀ η, (∀ b, ‖η b‖ < ρ) → |f η| ≤ G) → ∀ η, |cut f η| ≤ G := by
    intro f G hG hf η
    by_cases hη : ∀ b, ‖η b‖ < ρ
    · rw [hcut_in f η hη]
      exact hf η hη
    · simp only [hcut, if_neg hη, abs_zero]
      exact hG
  have h4 : (0 : ℝ) ≤ 4 * M := by linarith
  have hUM : ∀ η, |cut U η| ≤ 4 * M := hcut_size U _ h4 fun η hη =>
    (hbound 0 0 η hη).trans (by linarith)
  have hAM : ∀ η, |cut A η| ≤ 4 * M := hcut_size A _ h4 fun η hη => by
    simp only [hA]
    have := abs_sub (Ψ 1 0 η) (Ψ 0 0 η)
    have h1 := hbound 1 0 η hη
    have h2 := hbound 0 0 η hη
    linarith
  have hBM : ∀ η, |cut B η| ≤ 4 * M := hcut_size B _ h4 fun η hη => by
    simp only [hB]
    have := abs_sub (Ψ 0 1 η) (Ψ 0 0 η)
    have h1 := hbound 0 1 η hη
    have h2 := hbound 0 0 η hη
    linarith
  have hCM : ∀ η, |cut C η| ≤ 4 * M := hcut_size C _ h4 fun η hη => by
    simp only [hC]
    have h1 := hbound 1 1 η hη
    have h2 := hbound 1 0 η hη
    have h3 := hbound 0 1 η hη
    have h4 := hbound 0 0 η hη
    rw [abs_le] at h1 h2 h3 h4 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  have hsq_in : ∀ v w η, (∀ b, ‖η b‖ < ρ) → bilinearExponent (cut U) (cut A) (cut B) (cut C) v w η =
      bilinearExponent U A B C v w η := by
    intro v w η hη
    simp only [bilinearExponent, hcut_in _ η hη]
  set ε₀ : ℝ := m⁻¹ * (∑ b, ∑ b', Bf b * Real.exp (-(κ * d b b')) * Bg b') + Bc with hε
  have hkey : ∀ v w : ℝ, 0 ≤ v → v ≤ 1 → 0 ≤ w → w ≤ 1 →
      |gibbsMean μ (bilinearExponent (cut U) (cut A) (cut B) (cut C) v w)
            (fun ω => (cut A ω + w * cut C ω) * (cut B ω + v * cut C ω)) -
          gibbsMean μ (bilinearExponent (cut U) (cut A) (cut B) (cut C) v w)
            (fun ω => cut A ω + w * cut C ω) *
            gibbsMean μ (bilinearExponent (cut U) (cut A) (cut B) (cut C) v w)
              (fun ω => cut B ω + v * cut C ω) -
          gibbsMean μ (bilinearExponent (cut U) (cut A) (cut B) (cut C) v w) (cut C)| ≤ ε₀ := by
    intro v w h0 h1 h2 h3
    obtain ⟨Kv, hKv⟩ := hmixconv v w h0 h1 h2 h3
    have hv1 : 0 ≤ 1 - v := by linarith
    have hw1 : 0 ≤ 1 - w := by linarith
    have hf : ContDiff ℝ 1 fun ω => A ω + w * C ω := by
      have e1 : ContDiff ℝ 3 A := (hconv 1 0).smooth.sub (hconv 0 0).smooth
      have e2 : ContDiff ℝ 3 C :=
        (((hconv 1 1).smooth.sub (hconv 1 0).smooth).sub (hconv 0 1).smooth).add (hconv 0 0).smooth
      exact (e1.add (contDiff_const.mul e2)).of_le (by norm_num)
    have hg : ContDiff ℝ 1 fun ω => B ω + v * C ω := by
      have e1 : ContDiff ℝ 3 B := (hconv 0 1).smooth.sub (hconv 0 0).smooth
      have e2 : ContDiff ℝ 3 C :=
        (((hconv 1 1).smooth.sub (hconv 1 0).smooth).sub (hconv 0 1).smooth).add (hconv 0 0).smooth
      exact (e1.add (contDiff_const.mul e2)).of_le (by norm_num)
    have hbf : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b,
        bondGradNorm (fun ω => A ω + w * C ω) b η ≤ Bf b := by
      intro η hη b
      have e : (fun ω => A ω + w * C ω) = fun ζ =>
          (1 - w) * (Ψ 1 0 ζ - Ψ 0 0 ζ) + w * (Ψ 1 1 ζ - Ψ 0 1 ζ) := by
        funext ζ
        simp only [hA, hC]
        ring
      rw [e]
      have a1 := hBf 0 η hη b
      have a2 := hBf 1 η hη b
      refine (bondGradNorm_linComb_le (f := fun ζ => Ψ 1 0 ζ - Ψ 0 0 ζ) (g := fun ζ => Ψ 1 1 ζ - Ψ 0 1 ζ)
        ((hΨd 1 0).sub (hΨd 0 0)) ((hΨd 1 1).sub (hΨd 0 1)) hw1 h2 b η).trans ?_
      nlinarith
    have hbg : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b,
        bondGradNorm (fun ω => B ω + v * C ω) b η ≤ Bg b := by
      intro η hη b
      have e : (fun ω => B ω + v * C ω) = fun ζ =>
          (1 - v) * (Ψ 0 1 ζ - Ψ 0 0 ζ) + v * (Ψ 1 1 ζ - Ψ 1 0 ζ) := by
        funext ζ
        simp only [hB, hC]
        ring
      rw [e]
      have a1 := hBg 0 η hη b
      have a2 := hBg 1 η hη b
      refine (bondGradNorm_linComb_le (f := fun ζ => Ψ 0 1 ζ - Ψ 0 0 ζ) (g := fun ζ => Ψ 1 1 ζ - Ψ 1 0 ζ)
        ((hΨd 0 1).sub (hΨd 0 0)) ((hΨd 1 1).sub (hΨd 1 0)) hv1 h0 b η).trans ?_
      nlinarith
    have hc := hcov ι ρ m κ d _ Kv p hρ hm hκ hp hd hKv _ _ Bf Bg hf hg hbf hbg
    have hEc : Continuous (bilinearExponent U A B C v w) := by
      rw [hsq]
      exact ((continuous_const.mul ((continuous_const.mul (hΨc 0 0)).add (continuous_const.mul (hΨc 1 0)))).add
        (continuous_const.mul ((continuous_const.mul (hΨc 0 1)).add (continuous_const.mul (hΨc 1 1)))))
    have hmean : |ballExpectation r (bilinearExponent U A B C v w) C| ≤ Bc := by
      set Dn := ballDensity r (bilinearExponent U A B C v w) with hDn
      have hpos : 0 < ∫ η, Dn η := hZpos _ hEc
      simp only [ballExpectation]
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      have hb : ‖∫ η, C η * Dn η‖ ≤ ∫ η, Bc * Dn η := by
        refine norm_integral_le_of_norm_le ((hdens_int _ hEc).const_mul Bc)
          (Filter.Eventually.of_forall fun η => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hdens_nonneg _ η)]
        by_cases hη : ∀ b, ‖η b‖ < ρ
        · have := hBc η hη
          have e : C η = Ψ 1 1 η + Ψ 0 0 η - Ψ 1 0 η - Ψ 0 1 η := by
            simp only [hC]
            ring
          rw [e]
          exact mul_le_mul_of_nonneg_right this (hdens_nonneg _ η)
        · have : Dn η = 0 := by
            simp only [hDn, ballDensity]
            change rim η * _ = 0
            rw [hrim_zero η hη, zero_mul]
          have h0 : ballDensity r (bilinearExponent U A B C v w) η = 0 := this
          simp only [hDn, h0, mul_zero, le_refl]
      rw [integral_const_mul, Real.norm_eq_abs] at hb
      exact hb
    rw [hwm (bilinearExponent U A B C v w) _ (fun η => (A η + w * C η) * (B η + v * C η)) _ (hsq_in v w)
        (fun η hη => by simp only [hcut_in _ η hη]),
      hwm (bilinearExponent U A B C v w) _ (fun η => A η + w * C η) _ (hsq_in v w)
        (fun η hη => by simp only [hcut_in _ η hη]),
      hwm (bilinearExponent U A B C v w) _ (fun η => B η + v * C η) _ (hsq_in v w)
        (fun η hη => by simp only [hcut_in _ η hη]),
      hwm (bilinearExponent U A B C v w) _ C _ (hsq_in v w) (fun η hη => hcut_in C η hη)]
    simp only [ballCovariance] at hc
    have := abs_sub (ballExpectation r (bilinearExponent U A B C v w)
          (fun η => (A η + w * C η) * (B η + v * C η)) -
        ballExpectation r (bilinearExponent U A B C v w) (fun ω => A ω + w * C ω) *
          ballExpectation r (bilinearExponent U A B C v w) (fun ω => B ω + v * C ω))
        (ballExpectation r (bilinearExponent U A B C v w) C)
    simp only [hε]
    linarith
  have hfinal := hmix (BondField ι) μ (cut U) (cut A) (cut B) (cut C) (4 * M) ε₀ hμ0
    (hcut_meas U hUc.measurable) (hcut_meas A hAc.measurable) (hcut_meas B hBc'.measurable)
    (hcut_meas C hCc.measurable) hUM hAM hBM hCM hkey
  have c11 : ∀ η, (∀ b, ‖η b‖ < ρ) → bilinearExponent (cut U) (cut A) (cut B) (cut C) 1 1 η = Ψ 1 1 η := by
    intro η hη
    rw [hsq_in 1 1 η hη]
    simp only [bilinearExponent, hU, hA, hB, hC]
    ring
  have c00 : ∀ η, (∀ b, ‖η b‖ < ρ) → bilinearExponent (cut U) (cut A) (cut B) (cut C) 0 0 η = Ψ 0 0 η := by
    intro η hη
    rw [hsq_in 0 0 η hη]
    simp only [bilinearExponent, hU, hA, hB, hC]
    ring
  have c10 : ∀ η, (∀ b, ‖η b‖ < ρ) → bilinearExponent (cut U) (cut A) (cut B) (cut C) 1 0 η = Ψ 1 0 η := by
    intro η hη
    rw [hsq_in 1 0 η hη]
    simp only [bilinearExponent, hU, hA, hB, hC]
    ring
  have c01 : ∀ η, (∀ b, ‖η b‖ < ρ) → bilinearExponent (cut U) (cut A) (cut B) (cut C) 0 1 η = Ψ 0 1 η := by
    intro η hη
    rw [hsq_in 0 1 η hη]
    simp only [bilinearExponent, hU, hA, hB, hC]
    ring
  rw [hZeq _ _ c11, hZeq _ _ c00, hZeq _ _ c10, hZeq _ _ c01] at hfinal
  exact ⟨fun i j => hZpos _ (hΨc i j), hfinal⟩
end YangMills.Construction.ConvexPotentials
end
