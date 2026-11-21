import YangMills.Construction.ColdStepAtMirrorFrames.FirstPartOfAChartMotion
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponential
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
theorem conjugatedExpFirstOrder_of_logSmooth (hlog : ConjugatedExpLogSmooth) :
    ConjugatedExpFirstOrder := by
  obtain ⟨Θ, U, C, hU, hC, hdiag, hΘc, hexp, hΘ0, hb, hf0, hfd⟩ := hlog
  refine ⟨2 * C, by positivity, ?_⟩
  intro p α u v e hα hu hv hα0 hv0 hu1 hev
  let P : (Fin p → ℝ) → imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions :=
    fun τ => (u τ, v τ, u 0)
  have hP0 : P 0 = diagonalTriple (u 0) := by
    show (u 0, v 0, u 0) = _
    rw [hv0]
    rfl
  have hPc : ContDiffAt ℝ 1 P 0 := hu.prodMk (hv.prodMk contDiffAt_const)
  have hPd : HasFDerivAt P ((fderiv ℝ u 0).prod ((fderiv ℝ v 0).prod 0)) 0 :=
    (hu.differentiableAt (by norm_num)).hasFDerivAt.prodMk
      ((hv.differentiableAt (by norm_num)).hasFDerivAt.prodMk (hasFDerivAt_const _ _))
  have hUnb : U ∈ 𝓝 (P 0) := by rw [hP0]; exact hU.mem_nhds (hdiag _)
  have hΘd : DifferentiableAt ℝ Θ (P 0) :=
    ((hΘc.contDiffAt hUnb).differentiableAt (by norm_num))
  have hβ : HasFDerivAt (Θ ∘ P) ((fderiv ℝ Θ (P 0)).comp ((fderiv ℝ u 0).prod ((fderiv ℝ v 0).prod 0))) 0 :=
    hΘd.hasFDerivAt.comp (0 : Fin p → ℝ) hPd
  have hPU : ∀ᶠ τ in 𝓝 (0 : Fin p → ℝ), P τ ∈ U := hPc.continuousAt.eventually hUnb
  have hβ0 : (Θ ∘ P) 0 = 0 := by
    show Θ (P 0) = 0
    rw [hP0]; exact hΘ0 _
  have hsm : ∀ᶠ τ in 𝓝 (0 : Fin p → ℝ), ‖(Θ ∘ P) τ‖ < 1 := by
    have hc : ContinuousAt (Θ ∘ P) 0 := hβ.continuousAt
    have := hc.eventually (Metric.ball_mem_nhds ((Θ ∘ P) 0) one_pos)
    refine this.mono fun τ h => ?_
    rw [hβ0] at h
    simpa using h
  have hsa : ∀ᶠ τ in 𝓝 (0 : Fin p → ℝ), ‖α τ‖ < 1 := by
    have := hα.continuousAt.eventually (Metric.ball_mem_nhds (α 0) one_pos)
    refine this.mono fun τ h => ?_
    rw [hα0] at h
    simpa using h
  have heq : α =ᶠ[𝓝 0] Θ ∘ P := by
    filter_upwards [hev, hPU, hsm, hsa] with τ h1 h2 h3 h4
    have e1 : expUnit (Θ (P τ)) = expUnit (α τ) := by
      rw [hexp _ h2, h1]
    exact (BlockOffsets.expUnit_inj_of_norm_le_one e1 h3.le h4.le).symm
  have hfd' : fderiv ℝ α 0 = (fderiv ℝ Θ (P 0)).comp ((fderiv ℝ u 0).prod ((fderiv ℝ v 0).prod 0)) := by
    rw [heq.fderiv_eq]
    exact hβ.fderiv
  rw [hfd']
  set z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions :=
    (fderiv ℝ u 0 e, fderiv ℝ v 0 e, 0) with hz
  have e2 : ((fderiv ℝ Θ (P 0)).comp ((fderiv ℝ u 0).prod ((fderiv ℝ v 0).prod 0))) e = fderiv ℝ Θ (P 0) z := rfl
  have e3 : fderiv ℝ u 0 e + fderiv ℝ v 0 e = fderiv ℝ Θ 0 z := by
    rw [hf0, hz]
    simp
  rw [e2, e3, hP0]
  have h1 := hfd (u 0) z hu1
  refine h1.trans ?_
  have hzn : ‖z‖ ≤ ‖fderiv ℝ u 0 e‖ + ‖fderiv ℝ v 0 e‖ := by
    rw [hz]
    simp only [Prod.norm_def, norm_zero]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (max_le (le_add_of_nonneg_left (norm_nonneg _))
      (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hun := norm_nonneg (u 0)
  calc C * ‖u 0‖ * ‖z‖ ≤ C * ‖u 0‖ * (‖fderiv ℝ u 0 e‖ + ‖fderiv ℝ v 0 e‖) := by gcongr
    _ ≤ 2 * C * ‖u 0‖ * (‖fderiv ℝ u 0 e‖ + ‖fderiv ℝ v 0 e‖) := by
      have : 0 ≤ ‖fderiv ℝ u 0 e‖ + ‖fderiv ℝ v 0 e‖ := by positivity
      have h2 : 0 ≤ C * ‖u 0‖ * (‖fderiv ℝ u 0 e‖ + ‖fderiv ℝ v 0 e‖) := by positivity
      nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
