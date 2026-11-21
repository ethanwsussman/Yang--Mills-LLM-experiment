import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace SummableBounds
open BlockAverages ColdStepAtMirrorFrames
def InterpolatedFrameDecay (T : StepParameters) (Cz : ℝ) : Prop :=
  ∀ (x : ℝ) (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ), T.coupling ≤ x →
    IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
    ∀ d ∈ chordBonds (finiteCells F),
      ‖Interpolation.interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) d V‖ ≤ Cz * T.σ ∧
      IsBondAnalyticAt (Interpolation.interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) d) V ∧
      ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
        AreUnitVectors X →
        ‖bondDeriv (Interpolation.interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) d) V c X‖ ≤
          16 ^ k * T.chainParams.Kk k *
            Real.exp (-(T.chainParams.κ₂ * bondListDistance (enclosingCell d.1) c))
def interpolatedFrameDecayStatement : Prop :=
  ∃ Cz : ℝ → ℕ → ColdChainParameters → ℝ, (∀ a L c, 0 < Cz a L c) ∧
    EventuallyInParameters fun T => InterpolatedFrameDecay T (Cz T.a T.L T.chainParams)
end SummableBounds
end YangMills.Construction
end
