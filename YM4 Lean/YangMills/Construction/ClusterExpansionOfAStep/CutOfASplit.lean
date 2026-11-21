import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction
open ColdStepAtMirrorFrames StepSettings TorusFields TorusLumps Interpolation
namespace ClusterExpansionOfAStep.Restriction
section Tilted
variable {α : Type} [MeasurableSpace α] {μ : Measure α} {w f g : α → ℝ} {M : ℝ}
theorem abs_tiltedMean_le (hw : Integrable w μ) (hw0 : ∀ᵐ a ∂μ, 0 < w a) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hfM : ∀ᵐ a ∂μ, |f a| ≤ M) (hgM : ∀ᵐ a ∂μ, |g a| ≤ M)
    {H : α → ℝ} (hH : AEStronglyMeasurable H μ) {C : ℝ} (hC : ∀ᵐ a ∂μ, |H a| ≤ C) (t : ℝ)
    (hpos : 0 < ∫ a, w a * Real.exp (f a + t * g a) ∂μ) :
    |tiltedMean μ w f g H t| ≤ C := by
  have hone : Integrable (fun a => (1 : ℝ) * (w a * Real.exp (f a + t * g a))) μ :=
    integrable_mul_weight_exp (K := 1) hw hf hg hfM hgM aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun _ => by simp) t
  have hd : Integrable (fun a => w a * Real.exp (f a + t * g a)) μ := by simpa using hone
  have hHd := integrable_mul_weight_exp hw hf hg hfM hgM hH hC t
  unfold tiltedMean
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |∫ a, H a * (w a * Real.exp (f a + t * g a)) ∂μ|
      ≤ ∫ a, |H a * (w a * Real.exp (f a + t * g a))| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ a, C * (w a * Real.exp (f a + t * g a)) ∂μ := by
        refine integral_mono_ae hHd.abs (hd.const_mul _) ?_
        filter_upwards [hC, hw0] with a h1 h2
        have h3 : 0 < w a * Real.exp (f a + t * g a) := mul_pos h2 (Real.exp_pos _)
        rw [abs_mul, abs_of_pos h3]
        exact mul_le_mul_of_nonneg_right h1 h3.le
    _ = C * ∫ a, w a * Real.exp (f a + t * g a) ∂μ := integral_const_mul _ _
end Tilted
section Sums
variable {R : StepSetup} {n : ℕ} [NeZero n] {free : Finset (TorusBond (n * R.params.side))} {D : BlockDensitySplit R n free}
theorem abs_sum_integral_weightedMean_interpolatedDensity_le (hcore : LogIntegralExpInterpolationStatement)
    (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn)
    (hreg : D.IsRegular) (lam : ℝ) (S : Finset (TorusSite n)) {G : TorusSite n → FreeCoords free → ℝ}
    (hG : ∀ Y, AEBounded (volume.restrict (openBallsIn R free)) (G Y)) {C : ℝ}
    (hB : ∀ η ∈ openBallsIn R free, |∑ Y ∈ S, G Y η| ≤ C) :
    |∑ Y ∈ S, ∫ τ in (0 : ℝ)..1, weightedMean (D.interpolatedDensity lam τ) (G Y)| ≤ C := by
  have hBm : MeasurableSet (openBallsIn R free) := isOpen_openBallsIn.measurableSet
  obtain ⟨hμ, hw, hw0⟩ := cutoffProd_setup (R := R) (free := free) hρ hp
  have hPsi : AEBounded (volume.restrict (openBallsIn R free)) D.totalInteraction :=
    AEBounded.sum _ fun Y _ => aeBounded_interaction hreg Y
  have hQ : AEBounded (volume.restrict (openBallsIn R free))
      fun η => ∑ Y : TorusSite n, gaussianPart (R := R) lam Y η :=
    AEBounded.sum _ fun Y _ => aeBounded_gaussianPart lam Y
  have hf := hQ.neg
  have hg := hQ.sub hPsi
  obtain ⟨M, a, b⟩ := hf.exists_common_bound hg
  have hcr := hcore _ cutoffProd _ _ M hμ hw hw0 hf.1 hg.1 a b
  have hc : ∀ Y, Continuous fun τ => weightedMean (D.interpolatedDensity lam τ) (G Y) := fun Y =>
    continuous_weightedMean_interpolatedDensity hcore hρ hp hreg lam (hG Y)
  rw [← intervalIntegral.integral_finsetSum fun Y _ => (hc Y).intervalIntegrable 0 1]
  have hb : ∀ τ, |∑ Y ∈ S, weightedMean (D.interpolatedDensity lam τ) (G Y)| ≤ C := by
    intro τ
    simp only [weightedMean_interpolatedDensity_eq]
    rw [← tiltedMean_finset_sum S G hw hf.1 hg.1 a b (fun Y _ => (hG Y).1) (fun Y _ => (hG Y).2)]
    exact abs_tiltedMean_le hw hw0 hf.1 hg.1 a b (AEBounded.sum S fun Y _ => hG Y).1
      (ae_restrict_of_forall_mem hBm hB) τ (hcr.1 τ)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := C)
    (f := fun τ => ∑ Y ∈ S, weightedMean (D.interpolatedDensity lam τ) (G Y)) (fun τ _ => hb τ)
  simpa using this
theorem abs_sum_integral_weightedMean_perturbedDensity_le (hcore : LogIntegralExpInterpolationStatement)
    (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn)
    (hreg : D.IsRegular) (S : Finset (TorusSite n)) {G : TorusSite n → FreeCoords free → ℝ}
    (hG : ∀ Y, AEBounded (volume.restrict (openBallsIn R free)) (G Y)) {C : ℝ}
    (hB : ∀ η ∈ openBallsIn R free, |∑ Y ∈ S, G Y η| ≤ C) :
    |∑ Y ∈ S, ∫ ν in (0 : ℝ)..1, weightedMean (D.perturbedDensity ν) (G Y)| ≤ C := by
  have hBm : MeasurableSet (openBallsIn R free) := isOpen_openBallsIn.measurableSet
  obtain ⟨hμ, hw, hw0⟩ := cutoffProd_setup (R := R) (free := free) hρ hp
  have hPsi : AEBounded (volume.restrict (openBallsIn R free)) D.totalInteraction :=
    AEBounded.sum _ fun Y _ => aeBounded_interaction hreg Y
  have hΦ : AEBounded (volume.restrict (openBallsIn R free)) fun η => ∑ Y : TorusSite n, D.density Y η :=
    AEBounded.sum _ fun Y _ => aeBounded_density hreg Y
  have hf := hPsi.neg
  obtain ⟨M, a, b⟩ := hf.exists_common_bound hΦ
  have hcr := hcore _ cutoffProd _ _ M hμ hw hw0 hf.1 hΦ.1 a b
  have hc : ∀ Y, Continuous fun ν => weightedMean (D.perturbedDensity ν) (G Y) := fun Y =>
    continuous_weightedMean_perturbedDensity hcore hρ hp hreg (hG Y)
  rw [← intervalIntegral.integral_finsetSum fun Y _ => (hc Y).intervalIntegrable 0 1]
  have hb : ∀ ν, |∑ Y ∈ S, weightedMean (D.perturbedDensity ν) (G Y)| ≤ C := by
    intro ν
    simp only [weightedMean_perturbedDensity_eq]
    rw [← tiltedMean_finset_sum S G hw hf.1 hΦ.1 a b (fun Y _ => (hG Y).1) (fun Y _ => (hG Y).2)]
    exact abs_tiltedMean_le hw hw0 hf.1 hΦ.1 a b (AEBounded.sum S fun Y _ => hG Y).1
      (ae_restrict_of_forall_mem hBm hB) ν (hcr.1 ν)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := C)
    (f := fun ν => ∑ Y ∈ S, weightedMean (D.perturbedDensity ν) (G Y)) (fun ν _ => hb ν)
  simpa using this
theorem weightedMean_perturbedDensity_sub_const_add (hcore : LogIntegralExpInterpolationStatement)
    (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn)
    (hreg : D.IsRegular) (ν : ℝ) {G : FreeCoords free → ℝ}
    (hG : AEBounded (volume.restrict (openBallsIn R free)) G) (c : ℝ) :
    weightedMean (D.perturbedDensity ν) (fun η => G η - c) + c = weightedMean (D.perturbedDensity ν) G := by
  obtain ⟨hμ, hw, hw0⟩ := cutoffProd_setup (R := R) (free := free) hρ hp
  have hPsi : AEBounded (volume.restrict (openBallsIn R free)) D.totalInteraction :=
    AEBounded.sum _ fun Y _ => aeBounded_interaction hreg Y
  have hΦ : AEBounded (volume.restrict (openBallsIn R free)) fun η => ∑ Y : TorusSite n, D.density Y η :=
    AEBounded.sum _ fun Y _ => aeBounded_density hreg Y
  have hf := hPsi.neg
  obtain ⟨M, a, b⟩ := hf.exists_common_bound hΦ
  have hcr := hcore _ cutoffProd _ _ M hμ hw hw0 hf.1 hΦ.1 a b
  obtain ⟨hGm, K, hK⟩ := hG
  have hi1 := integrable_mul_weight_exp hw hf.1 hΦ.1 a b hGm hK ν
  have hi2 := integrable_mul_weight_exp (K := |c|) hw hf.1 hΦ.1 a b
    (aestronglyMeasurable_const (b := c)) (Filter.Eventually.of_forall fun _ => le_rfl) ν
  rw [weightedMean_perturbedDensity_eq, weightedMean_perturbedDensity_eq]
  unfold tiltedMean
  have hpos := (hcr.1 ν).ne'
  have e : ∫ a, (G a - c) * (cutoffProd (R := R) a *
        Real.exp (-D.totalInteraction a + ν * ∑ Y : TorusSite n, D.density Y a))
      ∂(volume.restrict (openBallsIn R free)) =
      (∫ a, G a * (cutoffProd (R := R) a *
          Real.exp (-D.totalInteraction a + ν * ∑ Y : TorusSite n, D.density Y a))
        ∂(volume.restrict (openBallsIn R free))) -
      c * ∫ a, cutoffProd (R := R) a *
          Real.exp (-D.totalInteraction a + ν * ∑ Y : TorusSite n, D.density Y a)
        ∂(volume.restrict (openBallsIn R free)) := by
    rw [← integral_const_mul, ← integral_sub hi1 hi2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => by simp only; ring)
  rw [e]
  field_simp
  ring
end Sums
section Restrict
variable {R : StepSetup} {n : ℕ} [NeZero n] (s : ChartSetting R n) (lam : ℝ) (X : Finset s.free)
theorem restrictTo_zero : s.restrictTo X 0 = 0 := by
  classical
  funext b
  simp [ChartSetting.restrictTo]
theorem restrictTo_univ (η : FreeCoords s.free) : s.restrictTo Finset.univ η = η := by
  classical
  funext b
  simp [ChartSetting.restrictTo]
theorem restrictedSplit_cost_zero (Y : TorusSite n) :
    (s.restrictedSplit lam X).cost Y 0 = s.blockCostAt Y 0 := by
  simp [ChartSetting.restrictedSplit, restrictTo_zero]
theorem restrictedSplit_logJacobian_zero (Y : TorusSite n) :
    (s.restrictedSplit lam X).logJacobian Y 0 = s.logJacobianAt Y 0 := by
  simp [ChartSetting.restrictedSplit, restrictTo_zero]
theorem sum_sum_freeBondsAt_sdiff (η : FreeCoords s.free) :
    ∑ Y : TorusSite n, ∑ b ∈ freeBondsAt s.free Y \ X, ‖η b‖ ^ 2 = ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2 := by
  classical
  have : ∀ Y : TorusSite n, ∑ b ∈ freeBondsAt s.free Y \ X, ‖η b‖ ^ 2 =
      ∑ b ∈ (Finset.univ \ X).filter (fun b : s.free => bondBlock (R := R) b.1 = Y), ‖η b‖ ^ 2 := by
    intro Y
    apply Finset.sum_congr _ fun _ _ => rfl
    ext b
    simp [freeBondsAt, and_comm]
  simp_rw [this]
  exact Finset.sum_fiberwise (Finset.univ \ X) (fun b : s.free => bondBlock (R := R) b.1) _
theorem restrictedSplit_totalCost_eq (w : FreeCoords s.free) :
    (s.restrictedSplit lam X).totalCost w =
      s.totalCost (s.restrictTo X w) + lam / 2 * ∑ b ∈ Finset.univ \ X, ‖w b‖ ^ 2 := by
  rw [← sum_sum_freeBondsAt_sdiff s X w, Finset.mul_sum]
  unfold BlockDensitySplit.totalCost ChartSetting.totalCost
  rw [← Finset.sum_add_distrib]
  rfl
theorem restrictedSplit_potential_eq (η : FreeCoords s.free) :
    (s.restrictedSplit lam X).potential η =
      s.potential (s.restrictTo X η) + R.coupling * lam / 2 * ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2 := by
  rw [← sum_sum_freeBondsAt_sdiff s X η]
  have h2 : s.potential (s.restrictTo X η) = ∑ Y : TorusSite n,
      (R.coupling * s.blockCostAt Y (s.restrictTo X η) - s.blockDensityAt Y (s.restrictTo X η) -
        s.logJacobianAt Y (s.restrictTo X η)) := rfl
  rw [h2, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Y _
  simp only [ChartSetting.restrictedSplit]
  ring
variable {X}
theorem restrictTo_add_smul_singleBond_of_not_mem {b : s.free} (hb : b ∉ X) (v τ : ℝ)
    (η : FreeCoords s.free) :
    s.restrictTo X (v • η + τ • singleBond b η) = s.restrictTo X (v • η) := by
  classical
  funext b'
  by_cases h : b' ∈ X
  · have hne : b' ≠ b := fun e => hb (e ▸ h)
    simp [ChartSetting.restrictTo, h, singleBond, hne]
  · simp [ChartSetting.restrictTo, h]
theorem deriv_restrictedSplit_totalCost_of_not_mem {b : s.free} (hb : b ∉ X) (v : ℝ) (η : FreeCoords s.free) :
    deriv (fun τ : ℝ => (s.restrictedSplit lam X).totalCost (v • η + τ • singleBond b η)) 0 =
      lam * v * ‖η b‖ ^ 2 := by
  classical
  set K : ℝ := s.totalCost (s.restrictTo X (v • η)) +
    lam / 2 * ∑ b' ∈ (Finset.univ \ X).erase b, ‖(v • η) b'‖ ^ 2 with hK
  have hmem : b ∈ Finset.univ \ X := by simp [hb]
  have hform : ∀ τ : ℝ, (s.restrictedSplit lam X).totalCost (v • η + τ • singleBond b η) =
      K + lam / 2 * ((v + τ) ^ 2 * ‖η b‖ ^ 2) := by
    intro τ
    rw [restrictedSplit_totalCost_eq, restrictTo_add_smul_singleBond_of_not_mem s hb,
      ← Finset.add_sum_erase _ _ hmem]
    have h1 : ‖(v • η + τ • singleBond b η) b‖ ^ 2 = (v + τ) ^ 2 * ‖η b‖ ^ 2 := by
      have : (v • η + τ • singleBond b η) b = (v + τ) • η b := by
        simp [singleBond, add_smul]
      rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h2 : ∑ b' ∈ (Finset.univ \ X).erase b, ‖(v • η + τ • singleBond b η) b'‖ ^ 2 =
        ∑ b' ∈ (Finset.univ \ X).erase b, ‖(v • η) b'‖ ^ 2 := by
      refine Finset.sum_congr rfl fun b' hb' => ?_
      have hne : b' ≠ b := (Finset.mem_erase.mp hb').1
      simp [singleBond, hne]
    rw [h1, h2, hK]
    ring
  simp_rw [hform]
  have hd : HasDerivAt (fun τ : ℝ => K + lam / 2 * ((v + τ) ^ 2 * ‖η b‖ ^ 2)) (lam * v * ‖η b‖ ^ 2) 0 := by
    have h0 : HasDerivAt (fun τ : ℝ => v + τ) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add v
    have h1 : HasDerivAt (fun τ : ℝ => (v + τ) ^ 2) (2 * v) 0 := by
      have h2 : HasDerivAt ((fun τ : ℝ => v + τ) ^ 2) (2 * v) 0 := by simpa using h0.pow 2
      exact h2
    have h3 := ((h1.mul_const (‖η b‖ ^ 2)).const_mul (lam / 2)).const_add K
    have e : lam * v * ‖η b‖ ^ 2 = lam / 2 * (2 * v * ‖η b‖ ^ 2) := by ring
    rw [e]
    exact h3
  exact hd.deriv
theorem restrictedSplit_interaction_sub_gaussianPart {Y : TorusSite n} (hY : ∀ b ∈ freeBondsAt s.free Y, b ∉ X)
    (η : FreeCoords s.free) :
    (s.restrictedSplit lam X).interaction Y η - gaussianPart lam Y η =
      (s.restrictedSplit lam X).logJacobian Y 0 - (s.restrictedSplit lam X).logJacobian Y η := by
  have h1 : ∀ b ∈ freeBondsAt s.free Y, ∫ v in (0 : ℝ)..1,
      deriv (fun τ : ℝ => (s.restrictedSplit lam X).totalCost (v • η + τ • singleBond b η)) 0 =
        lam / 2 * ‖η b‖ ^ 2 := by
    intro b hb
    simp_rw [deriv_restrictedSplit_totalCost_of_not_mem s lam (hY b hb)]
    have e : ∀ v : ℝ, lam * v * ‖η b‖ ^ 2 = (lam * ‖η b‖ ^ 2) * v := fun v => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  unfold BlockDensitySplit.interaction gaussianPart
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  ring
variable (X)
theorem deriv_restrictedSplit_totalCost_of_mem {b : s.free} (hb : b ∈ X) (v : ℝ) (η : FreeCoords s.free) :
    deriv (fun τ : ℝ => (s.restrictedSplit lam X).totalCost (v • η + τ • singleBond b η)) 0 =
      deriv (fun τ : ℝ => s.totalCost (v • s.restrictTo X η + τ • singleBond b (s.restrictTo X η))) 0 := by
  classical
  have hform : ∀ τ : ℝ, (s.restrictedSplit lam X).totalCost (v • η + τ • singleBond b η) =
      s.totalCost (v • s.restrictTo X η + τ • singleBond b (s.restrictTo X η)) +
        lam / 2 * ∑ b' ∈ Finset.univ \ X, ‖(v • η) b'‖ ^ 2 := by
    intro τ
    rw [restrictedSplit_totalCost_eq]
    have h1 : s.restrictTo X (v • η + τ • singleBond b η) =
        v • s.restrictTo X η + τ • singleBond b (s.restrictTo X η) := by
      funext b'
      by_cases h : b' ∈ X
      · by_cases e : b' = b
        · subst e
          simp [ChartSetting.restrictTo, h, singleBond]
        · simp [ChartSetting.restrictTo, h, singleBond, e]
      · have hne : b' ≠ b := fun e => h (e ▸ hb)
        simp [ChartSetting.restrictTo, h, singleBond, hne]
    have h2 : ∑ b' ∈ Finset.univ \ X, ‖(v • η + τ • singleBond b η) b'‖ ^ 2 =
        ∑ b' ∈ Finset.univ \ X, ‖(v • η) b'‖ ^ 2 := by
      refine Finset.sum_congr rfl fun b' hb' => ?_
      have hne : b' ≠ b := fun e => (Finset.mem_sdiff.mp hb').2 (e ▸ hb)
      simp [singleBond, hne]
    rw [h1, h2]
  simp_rw [hform]
  rw [deriv_add_const]
theorem restrictedSplit_interaction_of_mem {Y : TorusSite n} (hY : ∀ b ∈ freeBondsAt s.free Y, b ∈ X)
    (η : FreeCoords s.free) :
    (s.restrictedSplit lam X).interaction Y η = s.blockInteraction Y (s.restrictTo X η) := by
  have h1 : ∀ b ∈ freeBondsAt s.free Y, ∫ v in (0 : ℝ)..1,
      deriv (fun τ : ℝ => (s.restrictedSplit lam X).totalCost (v • η + τ • singleBond b η)) 0 =
      ∫ v in (0 : ℝ)..1,
        deriv (fun τ : ℝ => s.totalCost (v • s.restrictTo X η + τ • singleBond b (s.restrictTo X η))) 0 :=
    fun b hb => by simp_rw [deriv_restrictedSplit_totalCost_of_mem s lam X (hY b hb)]
  unfold BlockDensitySplit.interaction
  rw [Finset.sum_congr rfl h1, restrictedSplit_logJacobian_zero]
  rfl
theorem continuous_restrictTo : Continuous (s.restrictTo X) := by
  classical
  refine continuous_pi fun b => ?_
  unfold ChartSetting.restrictTo
  by_cases h : b ∈ X
  · simp only [h, if_true]
    exact continuous_apply b
  · simp only [h, if_false]
    exact continuous_const
theorem contDiff_restrictTo : ContDiff ℝ 1 (s.restrictTo X) := by
  classical
  refine contDiff_pi.mpr fun b => ?_
  unfold ChartSetting.restrictTo
  by_cases h : b ∈ X
  · simp only [h, if_true]
    exact contDiff_apply ℝ _ b
  · simp only [h, if_false]
    exact contDiff_const
theorem restrictTo_mem_openBallsIn {η : FreeCoords s.free} (hρ : 0 < R.ballRadius)
    (h : η ∈ openBallsIn R s.free) : s.restrictTo X η ∈ openBallsIn R s.free := by
  classical
  intro b
  by_cases hb : b ∈ X
  · simp only [ChartSetting.restrictTo, hb, if_true]
    exact h b
  · simp only [ChartSetting.restrictTo, hb, if_false]
    rw [coordNorm_eq_norm]
    simpa using hρ
theorem coordNorm_restrictTo_le {η : FreeCoords s.free} (hρ : 0 < R.ballRadius)
    (h : ∀ b, coordNorm (η b) ≤ R.ballRadius) (b : s.free) :
    coordNorm (s.restrictTo X η b) ≤ R.ballRadius := by
  classical
  by_cases hb : b ∈ X
  · simp only [ChartSetting.restrictTo, hb, if_true]
    exact h b
  · simp only [ChartSetting.restrictTo, hb, if_false]
    rw [coordNorm_eq_norm]
    simpa using hρ.le
theorem restrictedSplit_isRegular (hρ : 0 < R.ballRadius) (hreg : s.densitySplit.IsRegular) :
    (s.restrictedSplit lam X).IsRegular := by
  classical
  have hBm : MeasurableSet (openBallsIn R s.free) := isOpen_openBallsIn.measurableSet
  have hcm : Measurable (s.restrictTo X) := (continuous_restrictTo s X).measurable
  have hind : ∀ (h : FreeCoords s.free → ℝ), Measurable ((openBallsIn R s.free).indicator h) →
      Measurable ((openBallsIn R s.free).indicator fun η => h (s.restrictTo X η)) := by
    intro h hm
    have e : (openBallsIn R s.free).indicator (fun η => h (s.restrictTo X η)) =
        (openBallsIn R s.free).indicator (((openBallsIn R s.free).indicator h) ∘ s.restrictTo X) := by
      funext η
      by_cases hη : η ∈ openBallsIn R s.free
      · simp [Set.indicator_of_mem hη, Set.indicator_of_mem (restrictTo_mem_openBallsIn s X hρ hη)]
      · simp [Set.indicator_of_notMem hη]
    rw [e]
    exact (hm.comp hcm).indicator hBm
  obtain ⟨U, hUo, hUb, hC⟩ := hreg.cost_smooth
  obtain ⟨M, hM⟩ := hreg.bounded
  refine ⟨⟨s.restrictTo X ⁻¹' U, hUo.preimage (continuous_restrictTo s X), fun η hη => hUb _
    (coordNorm_restrictTo_le s X hρ hη), ?_⟩, fun Y => hind _ (hreg.measurable_logJacobian Y),
    fun Y => hind _ (hreg.measurable_density Y),
    ⟨M, fun η hη Y => hM _ (restrictTo_mem_openBallsIn s X hρ hη) Y⟩⟩
  have e : (s.restrictedSplit lam X).totalCost = fun w =>
      s.densitySplit.totalCost (s.restrictTo X w) + lam / 2 * ∑ b ∈ Finset.univ \ X, ‖w b‖ ^ 2 := by
    funext w
    exact restrictedSplit_totalCost_eq s lam X w
  rw [e]
  refine (hC.comp (contDiff_restrictTo s X).contDiffOn fun η hη => hη).add ?_
  apply ContDiff.contDiffOn
  refine contDiff_const.mul (ContDiff.sum fun b _ => ?_)
  exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ _ b)
end Restrict
end ClusterExpansionOfAStep.Restriction
end YangMills.Construction
end
