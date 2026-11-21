import YangMills.Construction.ClusterExpansionOfAStep.FunctionsNearTheBallsExtend
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.BallExtensions
open YangMills.Construction.ColdStepAtMirrorFrames
theorem contDiffExtensionNearBalls_holds : ContDiffExtensionNearBalls := by
  intro ι _ ρ k g U hρ hU hb hg
  have hcl : ∀ η : BondField ι, η ∈ Metric.closedBall (0 : BondField ι) ρ ↔ ∀ b, ‖η b‖ ≤ ρ := by
    intro η
    rw [mem_closedBall_zero_iff]
    exact pi_norm_le_iff_of_nonneg hρ.le
  have hKU : Metric.closedBall (0 : BondField ι) ρ ⊆ U := fun η hη => hb η ((hcl η).mp hη)
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall (0 : BondField ι) ρ).exists_cthickening_subset_open
    hU hKU
  rw [cthickening_closedBall hδ.le hρ.le, add_comm δ ρ] at hδU
  let f : ContDiffBump (0 : BondField ι) :=
    ⟨ρ + δ / 2, ρ + δ, by linarith, by linarith⟩
  refine ⟨fun η => f η * g η, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro η
    by_cases hη : η ∈ U
    · exact (f.contDiff.contDiffAt).mul (hg.contDiffAt (hU.mem_nhds hη))
    · have hout : η ∉ Metric.closedBall (0 : BondField ι) (ρ + δ) := fun h => hη (hδU h)
      have hnear : (Metric.closedBall (0 : BondField ι) (ρ + δ))ᶜ ∈ nhds η :=
        Metric.isClosed_closedBall.isOpen_compl.mem_nhds hout
      have h0 : (fun η => f η * g η) =ᶠ[nhds η] fun _ => (0 : ℝ) := by
        filter_upwards [hnear] with ζ hζ
        have : f ζ = 0 := by
          apply f.zero_of_le_dist
          have : ¬ dist ζ 0 ≤ ρ + δ := fun h => hζ (Metric.mem_closedBall.mpr h)
          linarith [not_le.mp this]
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  · intro η hη
    have hin : ‖η‖ ≤ ρ := (pi_norm_le_iff_of_nonneg hρ.le).mpr hη
    have hnear : Metric.ball (0 : BondField ι) (ρ + δ / 2) ∈ nhds η :=
      Metric.isOpen_ball.mem_nhds (by
        rw [mem_ball_zero_iff]
        linarith)
    filter_upwards [hnear] with ζ hζ
    have : f ζ = 1 := f.one_of_mem_closedBall (Metric.ball_subset_closedBall hζ)
    simp [this]
end YangMills.Construction.BallExtensions
end
