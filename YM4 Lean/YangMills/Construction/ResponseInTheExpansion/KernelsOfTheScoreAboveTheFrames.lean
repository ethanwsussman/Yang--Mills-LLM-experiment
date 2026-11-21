import YangMills.Construction.ResponseInTheExpansion.ColdPartAtTheParameters
import YangMills.Construction.ResponseInTheExpansion.TailOfAScore
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsAtTheFramesBetween
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
def scoreRemainderKernelBoundsStatement : Prop :=
  ∃ D : ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℝ, (∀ T l j, 0 < D T l j) ∧
    ColdStepAtMirrorFrames.EventuallyInParameters fun T =>
      ∀ (x : ℝ) (t : ℕ) (f : ColdStepAtMirrorFrames.LocalFamily) (F : BlockAverages.BlockFrame)
        (V : F.GaugeField F.top) (η : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells F)),
        T.coupling ≤ x → ColdStepAtMirrorFrames.IsCubicTopTorus T.L t T.n₀ F →
        ColdStepAtMirrorFrames.IsSmallCurvature (5 / 4 * T.σ) V → (∀ b, ‖η b‖ ≤ T.ballRadius) →
        ∀ (c₀ : F.Site F.top × Fin 4) (l j : ℕ)
          (b : Fin l → ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F)))
          (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
          (X : Fin j → BlockAverages.imaginaryQuaternions),
          1 ≤ l + j → (∀ i, ‖u i‖ = 1) → BlockAverages.AreUnitVectors X →
          Interpolation.HasDecayingKernelAt ((WeightedResponses.coldHalfLawAt T x f).scoreRemainderAt c₀)
            (D (Interpolation.rateParameters T) l j) (2 ^ 8 * T.κ) {c₀.1} η V b u c X
end YangMills.Construction.ResponseInTheExpansion
end
