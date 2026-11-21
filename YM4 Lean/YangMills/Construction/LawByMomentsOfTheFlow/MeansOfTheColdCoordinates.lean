import YangMills.Construction.ResponseInTheExpansion.MeanInTheColdSetting
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings YangMills.Construction.TorusFields
def coldCoordinateMeansStatement : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → T.ColdStepHolds → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusField n, IsCold (9 / 8 * T.threshold) V →
      ∃ e : ↥(coldChartSetting R V).free ≃ ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))),
        ∀ H : StepVariable (finiteCells (torusFrame R.params.side R.depth n)) → ℝ,
          weightedMean (YangMills.Construction.WeightedResponses.chartDensity (coldChartSetting R V))
              (fun η => H fun k => η (e.symm k)) =
            YangMills.Construction.ResponseInTheExpansion.coldStepMean R V H
end YangMills.Construction.MomentLaw
end
