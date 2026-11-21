import YangMills.Construction.ColdStepAtMirrorFrames.SmoothOnATube
import YangMills.Construction.SummableBoundsOfTheFlow.SlicesOfASmoothFunction
import YangMills.Construction.SummableBoundsOfTheFlow.TopDerivativesOfASmoothFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames SmoothSlices
namespace Estimates
theorem fieldDerivRegularity_holds (hS : IteratedFDerivSlices)
    (hT : UniformDerivBoundNearCompact) : fieldDerivRegularityStatement := by
  intro F ρ V
  have slice : ∀ (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (k : ℕ)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (η : StepVariable (finiteCells F)), JointlyContDiffOnBalls ρ V G → k ≤ 3 → (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ k (fun τ : Fin k → ℝ => G η (leftTranslate (bondSpread c X τ) V)) 0 := by
    intro G k c X η hG hk hη
    have h3 := hG k c X η hη
    have hemb : ContDiff ℝ 3 (fun τ : Fin k → ℝ => (τ, η)) := contDiff_id.prodMk contDiff_const
    have := ContDiffAt.comp
      (g := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => G q.2 (leftTranslate (bondSpread c X q.1) V))
      (0 : Fin k → ℝ) h3 hemb.contDiffAt
    exact ContDiffAt.of_le this (by exact_mod_cast hk)
  refine ⟨?_, ?_, ?_, slice, ?_⟩
  · intro G k c X hG hk η hη
    refine ContDiffAt.contDiffWithinAt ?_
    have h3 := hG k c X η fun b => (hη b).le
    exact hS.2.1 (Fin k → ℝ) (StepVariable (finiteCells F))
      (fun q => G q.2 (leftTranslate (bondSpread c X q.1) V)) k 1 (fun l => Pi.single l 1) η
      (ContDiffAt.of_le h3 (by exact_mod_cast (by omega : 1 + k ≤ 3)))
  · intro G k c X hG hk η hη
    refine ContinuousAt.continuousWithinAt ?_
    have h3 := hG k c X η fun b => (hη b).le
    have h0 : ContDiffAt ℝ 0 (fieldDeriv G V c X) η :=
      hS.2.1 (Fin k → ℝ) (StepVariable (finiteCells F))
        (fun q => G q.2 (leftTranslate (bondSpread c X q.1) V)) k 0 (fun l => Pi.single l 1) η
        (ContDiffAt.of_le h3 (by exact_mod_cast (by omega : 0 + k ≤ 3)))
    exact h0.continuousAt
  · intro G k c X hG hk
    have hK : IsCompact {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ ≤ ρ} := by
      have : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ ≤ ρ} =
          Set.pi Set.univ fun _ => Metric.closedBall 0 ρ := by
        ext η
        simp
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
    obtain ⟨r, M, hr, h⟩ := hT k (StepVariable (finiteCells F))
      (fun q => G q.2 (leftTranslate (bondSpread c X q.1) V)) _ hK (fun η hη => hG k c X η hη)
    refine ⟨M, fun η hη => ?_⟩
    have h1 := (h η hη).2 k hk 0 (Metric.mem_ball_self hr)
    have h2 := (iteratedFDeriv ℝ k
      (fun τ : Fin k → ℝ => G η (leftTranslate (bondSpread c X τ) V)) 0).le_opNorm (fun l => Pi.single l 1)
    have h3 : ∏ l : Fin k, ‖(Pi.single l 1 : Fin k → ℝ)‖ = 1 :=
      Finset.prod_eq_one fun l _ => by rw [Pi.norm_single, norm_one]
    rw [h3, mul_one] at h2
    exact h2.trans h1
  · intro α S G k c X η hG hk hη
    unfold fieldDeriv bondDeriv
    have h := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ)
      (f := fun a (τ : Fin k → ℝ) => G a η (leftTranslate (bondSpread c X τ) V))
      (u := S) (x := 0) (fun a ha => slice (G a) k c X η (hG a ha) hk hη)
    have h' : iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => ∑ a ∈ S, G a η (leftTranslate (bondSpread c X τ) V)) 0 =
        ∑ a ∈ S, iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => G a η (leftTranslate (bondSpread c X τ) V)) 0 := h
    rw [h']
    simp
end Estimates
end YangMills.Construction
end
