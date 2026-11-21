import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACut
import YangMills.Construction.ColdStepAtMirrorFrames.SmoothNearACompactSet
import YangMills.Construction.RunningCouplingSlope.CutLogarithmIsTwiceDifferentiable
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open ColdStepAtMirrorFrames
namespace LaplaceAsymptotics
theorem logCutoffIntegralContDiffTwo_of_radial (hcut : CutoffFactorIsRadialCutoff)
    (hnear : UniformDerivBoundNearCompactOfContinuous) (hmean : GibbsMeanDifferentiation) :
    LogCutoffIntegralContDiffTwo := by
  intro ι _ _ k ρ x p Q B hρ hp hQ hB
  have hw := hcut ρ p hρ hp
  set w : ℝ → ℝ := fun u => cutoffFactor ρ p (max u 0) with hwdef
  have hprod : ∀ A : BondField ι, radialWeightProd (cutoffFactor ρ p) A = radialWeightProd w A := by
    intro A
    unfold radialWeightProd
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [hwdef, max_eq_left (norm_nonneg (A b))]
  have hwc : Continuous w := hw.smooth.continuous
  have hWc : Continuous (fun A : BondField ι => radialWeightProd w A) := by
    unfold radialWeightProd
    exact continuous_finsetProd _ fun b _ => hwc.comp (continuous_norm.comp (continuous_apply b))
  set K : Set (BondField ι) := {A | ∀ b, ‖A b‖ ≤ ρ} with hK
  have hcomp : IsCompact K := by
    have : K = Set.pi Set.univ fun _ => Metric.closedBall 0 ρ := by
      ext A
      simp [hK]
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hm : MeasurableSet K := hcomp.isClosed.measurableSet
  set F : (Fin k → ℝ) × BondField ι → ℝ := fun z => Real.exp (-(x * Q z + B z)) with hF
  have hFs : ∀ A ∈ K, ContDiffAt ℝ 3 F (0, A) := fun A hA =>
    ((contDiffAt_const.mul (hQ A hA)).add (hB A hA)).neg.exp
  obtain ⟨s, M, hs, hcont, hsm⟩ := hnear k (BondField ι) F K hcomp hFs
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hWc.continuousOn
  set μ : Measure (BondField ι) := volume.restrict K with hμ
  have : IsFiniteMeasure μ := ⟨by
    rw [hμ, Measure.restrict_apply_univ]
    exact hcomp.measure_lt_top⟩
  set G : (Fin k → ℝ) → BondField ι → ℝ := fun τ A => radialWeightProd w A * F (τ, A) with hG
  have hopen : IsOpen (Metric.ball (0 : Fin k → ℝ) s) := Metric.isOpen_ball
  have hGc : ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) s, ContinuousOn (G τ) K := fun τ hτ =>
    hWc.continuousOn.mul (hcont τ hτ)
  have hdom : IsDominatedSmoothFamily μ 3 (Metric.ball (0 : Fin k → ℝ) s) (|C| * |M|) G := by
    refine ⟨fun τ hτ => (hGc τ hτ).aestronglyMeasurable hm, ?_, ?_⟩
    · refine ae_restrict_of_forall_mem hm fun A hA => ?_
      exact contDiffOn_const.mul (hsm A hA).1
    · refine ae_restrict_of_forall_mem hm fun A hA j hj τ hτ => ?_
      have hat : ContDiffAt ℝ j (fun τ => F (τ, A)) τ :=
        (((hsm A hA).1.of_le (by exact_mod_cast hj)).contDiffAt (hopen.mem_nhds hτ))
      have e : (fun τ => G τ A) = radialWeightProd w A • fun τ => F (τ, A) := by
        funext τ
        simp [hG]
      rw [e, iteratedFDeriv_const_smul_apply hat, norm_smul]
      have h1 : ‖radialWeightProd w A‖ ≤ |C| := (hC A hA).trans (le_abs_self C)
      have h2 : ‖iteratedFDeriv ℝ j (fun τ => F (τ, A)) τ‖ ≤ |M| :=
        ((hsm A hA).2 j hj τ hτ).trans (le_abs_self M)
      exact mul_le_mul h1 h2 (norm_nonneg _) (abs_nonneg _)
  have hI := (hmean.1 (BondField ι) μ k 3 _ _ G hopen hdom).1
  have hI2 : ContDiffAt ℝ 2 (fun τ => ∫ A, G τ A ∂μ) 0 :=
    (hI.contDiffAt (Metric.ball_mem_nhds _ hs)).of_le (by norm_num)
  have hnn : ∀ A : BondField ι, 0 ≤ radialWeightProd w A := fun A =>
    Finset.prod_nonneg fun b _ => by
      rcases lt_or_ge ‖A b‖ ρ with h | h
      · exact (hw.pos _ (norm_nonneg _) h).le
      · exact (hw.zero _ h).ge
  have hint : Integrable (G 0) μ := by
    refine Integrable.of_bound ((hGc 0 (Metric.mem_ball_self hs)).aestronglyMeasurable hm)
      (|C| * |M|) ?_
    filter_upwards [hdom.norm_iteratedFDeriv_le] with A hA
    have := hA 0 (by norm_num) 0 (Metric.mem_ball_self hs)
    simpa using this
  have hpos : 0 < ∫ A, G 0 A ∂μ := by
    rw [hμ, setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun A => mul_nonneg (hnn A) (Real.exp_pos _).le) hint]
    have hsub : Metric.ball (0 : BondField ι) ρ ⊆ Function.support (G 0) ∩ K := by
      intro A hA
      have hlt : ∀ b, ‖A b‖ < ρ := fun b =>
        (norm_le_pi_norm A b).trans_lt (mem_ball_zero_iff.mp hA)
      refine ⟨?_, fun b => (hlt b).le⟩
      have : 0 < radialWeightProd w A := Finset.prod_pos fun b _ => hw.pos _ (norm_nonneg _) (hlt b)
      exact (mul_pos this (Real.exp_pos _)).ne'
    exact (Metric.measure_ball_pos volume 0 hρ).trans_le (measure_mono hsub)
  have e : logCutoffIntegral ρ p x Q B = fun τ => Real.log (∫ A, G τ A ∂μ) := by
    funext τ
    unfold logCutoffIntegral
    congr 1
    rw [hμ, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
      simp only [hG, hF, hprod A]
    · intro A hA
      have : radialWeightProd w A = 0 := by
        simp only [hK, Set.mem_ofPred_eq, not_forall, not_le] at hA
        obtain ⟨b, hb⟩ := hA
        exact Finset.prod_eq_zero (Finset.mem_univ b) (hw.zero _ hb.le)
      simp [hG, this]
  rw [e]
  exact hI2.log hpos.ne'
end LaplaceAsymptotics
end YangMills.Construction
end
