import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheCostPart
import YangMills.Construction.ResponseInTheExpansion.ColdImageAboveTheFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open RenormalizationStepParameters StepSettings TorusLumps TorusFields StepCosts BlockAverages ColdStepAtMirrorFrames
def coldHalfLawIsLawStatement : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → T.ColdStepHolds → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusField n, IsCold (9 / 8 * T.threshold) V →
      Dilation.IsBallLaw R.ballRadius (coldHalfLawOf R).radialWeight
        ((coldHalfLawOf R).exponent (coldTopField R V)) ∧
      Continuous (coldFieldAboveFrames R V) ∧
      (∀ k : StepVariable (finiteCells (torusFrame R.params.side R.depth n)), (∀ b, ‖k b‖ < R.ballRadius) →
        ∃ η : FreeCoords (coldChartSetting R V).free, (∀ b, coordNorm (η b) < R.ballRadius) ∧
          (coldChartSetting R V).field η = coldFieldAboveFrames R V k) ∧
      (∀ G : TorusField (n * R.params.side) → ℝ, (∀ W, IsCold R.params.threshold W → ContDiffThreeAt G W) →
        ContinuousOn (fun k => G (coldFieldAboveFrames R V k))
          {k : StepVariable (finiteCells (torusFrame R.params.side R.depth n)) | ∀ b, ‖k b‖ < R.ballRadius}) ∧
      (open Classical in ∀ (g : (torusFrame R.params.side R.depth n).Site (torusFrame R.params.side R.depth n).depth → ℝ)
          (Y : TorusSite n),
        ∑ y ∈ (sitesOfCells (finiteCells (torusFrame R.params.side R.depth n))
            (torusFrame R.params.side R.depth n).depth).filter
            (fun y => enclosingCell y =
              torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top Y), g y =
          ∑ x ∈ sitesInBlocks R.params.side {Y},
            g (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).depth x))
end YangMills.Construction.ResponseInTheExpansion
end
