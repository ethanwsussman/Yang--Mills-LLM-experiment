import YangMills.Construction.Matrices.HaarExpChartDensityProof
import YangMills.Construction.ClusterExpansionOfAStep.LogOfTheHaarDensityIsSmooth
import YangMills.Construction.Matrices.UnitaryLogarithmClosedFormProof
import Mathlib
set_option autoImplicit false
noncomputable section
open FormalMultilinearSeries
namespace YangMills.Construction.HaarDensity
open ColdStepAtMirrorFrames
def sincSquareCoeff (q : ℕ) : ℝ := (-1) ^ q / ((2 * q + 1).factorial : ℝ)
def sincOfSquare : ℝ → ℝ := ofScalarsSum sincSquareCoeff
theorem radius_ofScalars_sincSquareCoeff : (ofScalars ℝ sincSquareCoeff).radius = ⊤ := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.HaarExpChart.sincSeries_radius <;> assumption
theorem contDiff_sincOfSquare : ContDiff ℝ 3 sincOfSquare := by
  have hball := (ofScalars ℝ sincSquareCoeff).hasFPowerSeriesOnBall
    (by rw [radius_ofScalars_sincSquareCoeff]; simp)
  have hanalytic := hball.analyticOnNhd
  rw [radius_ofScalars_sincSquareCoeff] at hanalytic
  have huniv : AnalyticOnNhd ℝ sincOfSquare Set.univ := fun x _ => hanalytic x (by simp)
  exact huniv.contDiff
theorem sinc_eq_sincOfSquare (r : ℝ) : Real.sinc r = sincOfSquare (r ^ 2) := by
  by_cases hr : r = 0
  · subst hr
    have hzero := ofScalarsSum_zero (E := ℝ) sincSquareCoeff
    simp only [sincOfSquare]
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, hzero]
    simp [sincSquareCoeff]
  · have hsum := (Real.hasSum_sin r).div_const r
    have hterm : (fun q : ℕ => (-1 : ℝ) ^ q * r ^ (2 * q + 1) / ((2 * q + 1).factorial : ℝ) / r) =
        fun q => sincSquareCoeff q • (r ^ 2) ^ q := by
      funext q
      unfold sincSquareCoeff
      rw [smul_eq_mul, pow_succ, ← pow_mul]
      field_simp
    rw [hterm] at hsum
    rw [Real.sinc_of_ne_zero hr, ← hsum.tsum_eq]
    simp only [sincOfSquare, ofScalarsSum_eq_tsum]
theorem sinc_pos_of_lt_pi {r : ℝ} (hnonneg : 0 ≤ r) (hr : r < Real.pi) : 0 < Real.sinc r := by apply _root_.YangMills.SharedProofs.p1819 <;> assumption
theorem logHaarDensityContDiffOnBall_holds : logHaarDensityContDiffOnBall := by
  intro v hv
  have hnear : (fun w => Real.log (haarLogDensity w)) =ᶠ[nhds v]
      fun w => Real.log (sincOfSquare (‖w‖ ^ 2) ^ 2 / (2 * Real.pi ^ 2)) := by
    have hlt : ∀ᶠ w in nhds v, ‖w‖ < Real.pi :=
      continuous_norm.continuousAt.eventually_lt continuousAt_const hv
    filter_upwards [hlt] with w hw
    unfold haarLogDensity
    rw [if_pos hw, sinc_eq_sincOfSquare]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hnear
  have hinner : ContDiffAt ℝ 3 (fun w : EuclideanSpace ℝ (Fin 3) => sincOfSquare (‖w‖ ^ 2)) v :=
    (contDiff_sincOfSquare.comp (contDiff_norm_sq ℝ)).contDiffAt
  refine ContDiffAt.log ((hinner.pow 2).div_const _) ?_
  have hsinc := sinc_pos_of_lt_pi (norm_nonneg v) hv
  rw [sinc_eq_sincOfSquare] at hsinc
  positivity
end YangMills.Construction.HaarDensity
end
