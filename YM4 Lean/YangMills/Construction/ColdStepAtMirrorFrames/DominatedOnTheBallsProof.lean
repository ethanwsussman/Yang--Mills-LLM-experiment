import YangMills.Construction.ColdStepAtMirrorFrames.DominatedOnTheBalls
import YangMills.Construction.ColdStepAtMirrorFrames.SmoothNearACompactSet
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem dominatedFamilyOnClosedBalls_of_uniformDerivBound
    (hT : UniformDerivBoundNearCompactOfContinuous) : DominatedFamilyOnClosedBalls := by
  intro ι _ k ρ μ G hμ hG
  set K : Set (BondField ι) := {η | ∀ b, ‖η b‖ ≤ ρ} with hK
  have hcomp : IsCompact K := by
    have : K = Set.pi Set.univ fun _ => Metric.closedBall 0 ρ := by
      ext η
      simp [hK]
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hKK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hcomp
  obtain ⟨r, M, hr, hcont, hsm⟩ := hT k (ℝ × BondField ι) G (Set.Icc (0 : ℝ) 1 ×ˢ K) hKK
    (fun z hz => hG z.1 z.2 hz.1 hz.2)
  refine ⟨r, M, hr, fun v hv => ⟨fun τ hτ => ?_, ?_, ?_⟩⟩
  · have hm : MeasurableSet K := hcomp.isClosed.measurableSet
    have hc : ContinuousOn (fun η => G (τ, v, η)) K := by
      have h1 := hcont τ hτ
      have h2 : ContinuousOn (fun η : BondField ι => (v, η)) K := by fun_prop
      exact h1.comp h2 fun η hη => ⟨hv, hη⟩
    have h1 : AEStronglyMeasurable (fun η => G (τ, v, η)) (μ.restrict K) :=
      hc.aestronglyMeasurable hm
    have h2 : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem hμ
    rwa [h2] at h1
  · filter_upwards [hμ] with η hη
    exact (hsm (v, η) ⟨hv, hη⟩).1
  · filter_upwards [hμ] with η hη
    exact (hsm (v, η) ⟨hv, hη⟩).2
end YangMills.Construction.ColdStepAtMirrorFrames
end
