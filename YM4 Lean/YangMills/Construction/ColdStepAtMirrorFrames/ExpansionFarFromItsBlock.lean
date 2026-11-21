import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def ExpansionOffBlockDecayAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → ∀ star : Bool,
      ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
        (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ < T.ballRadius) → 1 ≤ k → k ≤ 3 → AreUnitVectors X →
        |bondDeriv (cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y η) V c X| ≤
          (T.L : ℝ) ^ 4 * T.Ct * (if k = 3 then T.energyRatio else T.E) *
          (1 / torusDecayFactor T.L T.decayRate ((T.L : ℝ) * bondSpan Y c / 16) +
            Real.exp (-(2 ^ 6 * T.κ * bondSpan Y c)))
def ExpansionOffBlockDecay : Prop := EventuallyInParameters ExpansionOffBlockDecayAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
