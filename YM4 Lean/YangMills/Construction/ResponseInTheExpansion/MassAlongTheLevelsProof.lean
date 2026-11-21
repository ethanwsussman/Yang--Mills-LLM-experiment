import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfAStepAddUp
import YangMills.Construction.ClusterExpansionOfAStep.TheImageIsAnArray
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsBorel
import YangMills.Construction.ResponseInTheExpansion.MassAlongTheLevels
import YangMills.Construction.ResponseInTheExpansion.MeanOfScoresOverAStep
import YangMills.Construction.ResponseInTheExpansion.TheStepDensity
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings TorusLumps TorusFields RenormalizationStepParameters WeightedResponses StepFloors StepCosts ClusterExpansionOfAStep
namespace StateMass
variable {n : ℕ} [NeZero n]
private theorem kernelImage_eq_integral (ℓ : TorusLumps.StepParameters) (y : ℝ) (D : TorusFunctional)
    (V : TorusField n) :
    kernelImage ℓ y D n V = ∫ W : TorusField (n * ℓ.side), D (n * ℓ.side) W *
      averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
        (readAtLevel (stepBlockFrame ℓ.side n) 1 V) ∂(fieldHaar (n * ℓ.side)) := by
  simp only [kernelImage, NeZero.ne n, dite_false]
private theorem averagedKernel_eq_sum (ℓ : TorusLumps.StepParameters) (y : ℝ) (W : TorusField (n * ℓ.side))
    (V : TorusField n) :
    averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) =
      ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V := by
  classical
  unfold averagedKernel stepTransitionDensity
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
private theorem lintegral_averagedKernel_eq_one (hO : ScoreProductStepMean) (hS : StepTransitionDensityBounds)
    (ℓ : TorusLumps.StepParameters) (hfit : ℓ.Admissible) (y : ℝ) (W : TorusField (n * ℓ.side)) :
    ∫⁻ V : TorusField n, ENNReal.ofReal (averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
      (readAtLevel (stepBlockFrame ℓ.side n) 1 V)) ∂(fieldHaar n) = 1 := by
  obtain ⟨C, hC⟩ := (hS ℓ y n).2
  have hpk : Measurable fun V : TorusField n => (W, V) := measurable_prodMk_left
  have hint : ∀ b : BaseChoice ℓ.side n,
      Integrable (fun V : TorusField n => stepTransitionDensity ℓ y W b V) (fieldHaar n) := fun b =>
    Integrable.of_bound (((hS ℓ y n).1 b).comp hpk).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun V => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hC W b V).1]
        exact (hC W b V).2)
  have hsum : ∫ V : TorusField n, ∑ b : BaseChoice ℓ.side n, stepTransitionDensity ℓ y W b V ∂(fieldHaar n) = 1 := by
    rw [integral_finsetSum _ fun b _ => hint b]
    have h := hO ℓ hfit hfit.depth_lt y n W 0 (fun i => i.elim0) (fun i => i.elim0) (fun _ i => i.elim0)
    simpa using h
  simp_rw [averagedKernel_eq_sum]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_finsetSum _ fun b _ => hint b)
    (Filter.Eventually.of_forall fun V => Finset.sum_nonneg fun b _ => (hC W b V).1), hsum, ENNReal.ofReal_one]
private theorem lintegral_kernelImage (hO : ScoreProductStepMean) (hS : StepTransitionDensityBounds)
    (hB : BondKernelBorel) (ℓ : TorusLumps.StepParameters) (hfit : ℓ.Admissible) (y : ℝ) (D : TorusFunctional)
    (hm : Measurable (D (n * ℓ.side))) (h0 : ∀ W, 0 ≤ D (n * ℓ.side) W)
    (hi : ∀ V : TorusField n, Integrable (fun W : TorusField (n * ℓ.side) => D (n * ℓ.side) W *
      averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
        (readAtLevel (stepBlockFrame ℓ.side n) 1 V)) (fieldHaar (n * ℓ.side))) :
    ∫⁻ V : TorusField n, ENNReal.ofReal (kernelImage ℓ y D n V) ∂(fieldHaar n) =
      ∫⁻ W : TorusField (n * ℓ.side), ENNReal.ofReal (D (n * ℓ.side) W) ∂(fieldHaar (n * ℓ.side)) := by
  have hker : Measurable fun q : TorusField (n * ℓ.side) × TorusField n =>
      averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 q.1)
        (readAtLevel (stepBlockFrame ℓ.side n) 1 q.2) :=
    (hB ℓ y n).2.2.2.2.2.2.1
  have hk0 : ∀ (W : TorusField (n * ℓ.side)) (V : TorusField n),
      0 ≤ averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
        (readAtLevel (stepBlockFrame ℓ.side n) 1 V) := by
    intro W V
    rw [averagedKernel_eq_sum]
    obtain ⟨C, hC⟩ := (hS ℓ y n).2
    exact Finset.sum_nonneg fun b _ => (hC W b V).1
  have hjoint : Measurable (Function.uncurry fun (V : TorusField n) (W : TorusField (n * ℓ.side)) =>
      ENNReal.ofReal (D (n * ℓ.side) W) *
        ENNReal.ofReal (averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
          (readAtLevel (stepBlockFrame ℓ.side n) 1 V))) := by
    have h1 : Measurable fun q : TorusField n × TorusField (n * ℓ.side) => ENNReal.ofReal (D (n * ℓ.side) q.2) :=
      (hm.comp measurable_snd).ennreal_ofReal
    have h2 : Measurable fun q : TorusField n × TorusField (n * ℓ.side) => ENNReal.ofReal
        (averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 q.2)
          (readAtLevel (stepBlockFrame ℓ.side n) 1 q.1)) :=
      (hker.comp measurable_swap).ennreal_ofReal
    exact h1.mul h2
  calc ∫⁻ V : TorusField n, ENNReal.ofReal (kernelImage ℓ y D n V) ∂(fieldHaar n)
      = ∫⁻ V : TorusField n, ∫⁻ W : TorusField (n * ℓ.side), ENNReal.ofReal (D (n * ℓ.side) W) *
          ENNReal.ofReal (averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
            (readAtLevel (stepBlockFrame ℓ.side n) 1 V))
          ∂(fieldHaar (n * ℓ.side)) ∂(fieldHaar n) := by
        refine lintegral_congr fun V => ?_
        rw [kernelImage_eq_integral, ofReal_integral_eq_lintegral_ofReal (hi V)
          (Filter.Eventually.of_forall fun W => mul_nonneg (h0 W) (hk0 W V))]
        exact lintegral_congr fun W => ENNReal.ofReal_mul (h0 W)
    _ = ∫⁻ W : TorusField (n * ℓ.side), ∫⁻ V : TorusField n, ENNReal.ofReal (D (n * ℓ.side) W) *
          ENNReal.ofReal (averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
            (readAtLevel (stepBlockFrame ℓ.side n) 1 V))
          ∂(fieldHaar n) ∂(fieldHaar (n * ℓ.side)) :=
        lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ W : TorusField (n * ℓ.side), ENNReal.ofReal (D (n * ℓ.side) W) ∂(fieldHaar (n * ℓ.side)) := by
        refine lintegral_congr fun W => ?_
        have hpk : Measurable fun V : TorusField n => (W, V) := measurable_prodMk_left
        have hkm : Measurable fun V : TorusField n => ENNReal.ofReal
            (averagedKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
              (readAtLevel (stepBlockFrame ℓ.side n) 1 V)) :=
          (hker.comp hpk).ennreal_ofReal
        rw [lintegral_const_mul _ hkm, lintegral_averagedKernel_eq_one hO hS ℓ hfit y W, mul_one]
private theorem stateLIntegral_step_eq (hA : coarseStatesSumStatement) (hI : KernelImageIsDensity)
    (hO : ScoreProductStepMean) (hS : StepTransitionDensityBounds) (hB : BondKernelBorel)
    (R : StepSetup) (hR : R.IsWellPosed) (hA' : R.IsSymmetricWeight) (h : CoarseLabelFacts R) (lam x'' : ℝ)
    (hn : IsBlockTorusSide R.params n) :
    stateLIntegral R (n * R.params.side) (fun _ _ _ => 1) =
      stateLIntegral (nextStepSetup R h lam x'') n fun _ _ _ => 1 := by
  have hL1 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne R.params.side)
  have hn₀ : R.params.n₀ ≤ n := by
    have h1 := hn.2
    exact (Nat.le_mul_of_pos_left _ (by omega)).trans h1
  have hnL : R.params.n₀ ≤ n * R.params.side := hn₀.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hblock : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Nat.dvd_mul_left _ _, by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_right _ hn₀⟩
  obtain ⟨hm, h0, -, -⟩ := hA' (n * R.params.side) hnL
  have hrow : HasExpansion R.params R.depth R.coupling R.functional :=
    ⟨hA', R.density, hR.hasExpansions.1, R.labels, R.labelWeight, R.clusterFactor, R.siteDensity,
      hR.hasExpansions.2⟩
  have hi := (hI R.params hR.admissible R.depth R.coupling R.functional hR.coupling_pos hR.range_ge_base
    hrow n hn₀).1
  have hleft : stateLIntegral R (n * R.params.side) (fun _ _ _ => 1) =
      ∫⁻ W : TorusField (n * R.params.side), ENNReal.ofReal (R.functional (n * R.params.side) W)
        ∂(fieldHaar (n * R.params.side)) := by
    unfold stateLIntegral
    refine lintegral_congr fun W => ?_
    simp only [mul_one]
    exact hR.hasExpansions.2.sum (n * R.params.side) hblock W
  have hright : stateLIntegral (nextStepSetup R h lam x'') n (fun _ _ _ => 1) =
      ∫⁻ V : TorusField n, ENNReal.ofReal (kernelImage R.params R.coupling R.functional n V) ∂(fieldHaar n) := by
    unfold stateLIntegral
    refine lintegral_congr fun V => ?_
    simp only [mul_one]
    rw [← hA R hR n hn V]
    refine Finset.sum_congr rfl fun Y _ => lintegral_congr fun ω => ?_
    show ENNReal.ofReal (coarseWeightExpansion R n V Y ω) = _
    simp only [coarseWeightExpansion, NeZero.ne n, dite_false]
  rw [hleft, hright, lintegral_kernelImage hO hS hB R.params hR.admissible R.coupling R.functional hm h0 hi]
private theorem isWellPosed_of_onParameters {T : ParameterAssignment} (hT : T.Admissible) {y : ℝ} (hy₀ : T.floorMin ≤ y)
    (hy₁ : 1 ≤ y) {R : StepSetup} (hon : R.OnParameters T y) (hmoved : |R.nextCoupling - R.coupling| ≤ 2 * T.B)
    (hArr : R.IsSymmetricWeight)
    (hF : T.FloorConditions (2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17) 1 R.coupling) : R.IsWellPosed := by
  have hparams := hon.params_eq
  have hfit : R.params.Admissible := hparams ▸ hT.fits y hy₀
  have hxpos : 0 < R.coupling := lt_of_lt_of_le one_pos (hy₁.trans hon.le_coupling)
  obtain ⟨_, hstable⟩ := hF.stable_nearby
  obtain ⟨_, _, hr1, hr2⟩ := hstable _ hmoved
  have hr : (2 : ℝ) ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 ≤ clusterRange R.coupling := hF.range_ge
  have hr' : 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 ≤ clusterRange R.coupling := by exact_mod_cast hr
  have hLL : R.params.side = T.side := by
    rw [hparams]
    rfl
  have hNN : R.params.n₀ = T.n₀ := by
    rw [hparams]
    rfl
  have hρ : R.ballRadius = T.ballRadius := by
    unfold StepSetup.ballRadius
    rw [hparams]
    rfl
  have hcut : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn := by
    rw [hρ, hon.barrierFn_eq]
    exact hT.cut
  refine ⟨hon.isStep.1, hfit, hcut, hr1, hr2, ?_, ?_, ?_, hxpos, hArr⟩
  · show 2 ^ 16 ≤ clusterRange R.nextCoupling
    omega
  · show 2 ^ 40 * R.params.side ≤ clusterRange R.coupling
    omega
  · show 4 * R.params.n₀ + 2 ^ 16 ≤ clusterRange R.coupling
    omega
abbrev _root_.YangMills.SharedProofs.p3707 := @isWellPosed_of_onParameters
theorem stateMassPreservedByStep_holds (hA : coarseStatesSumStatement) (hI : KernelImageIsDensity)
    (hO : ScoreProductStepMean) (hS : StepTransitionDensityBounds) (hB : BondKernelBorel)
    (hFl : EventuallyFloorConditions) : StateMassPreservedByStep := by
  unfold StateMassPreservedByStep HoldsAtEveryStep
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ K => ?_⟩
  have hCpos : (0 : ℝ) < 2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17 := by positivity
  obtain ⟨yF, hyF⟩ := hFl T hT _ 1 hCpos one_pos
  refine ⟨max (max T.floorMin yF) 1, fun y hy R A _ hAt hArr h x'' n _ hn => ?_⟩
  have h1 : T.floorMin ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have h2 : yF ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have h3 : (1 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
  have hon := hAt.onFamily
  have hR := isWellPosed_of_onParameters hT h1 h3 hon hAt.abs_sub_le hArr (hyF R.coupling (h2.trans hon.le_coupling))
  exact stateLIntegral_step_eq hA hI hO hS hB R hR hArr h T.lam x'' hn
end StateMass
end YangMills.Construction.ResponseInTheExpansion
end
