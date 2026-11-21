import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTop
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def CentredExpansionNearUniformTopAt (T : StepParameters) (R : ℕ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → ∀ star : Bool,
    ∀ Y : F.Cell, IsNearUniformAbout (5 / 4 * T.σ) R V Y →
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        |cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y η V| ≤
          2⁻¹ ^ 8 * T.E / torusDecayFactor T.L T.decayRate T.blockIndex) ∧
      (∀ (η : StepVariable (finiteCells F)) (c : Fin 1 → F.Site F.top × Fin 4) (X : Fin 1 → imaginaryQuaternions),
        (∀ b, ‖η b‖ < T.ballRadius) → AreUnitVectors X → bondListDistance Y c ≤ T.blockIndex →
        |bondDeriv (cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y η) V c X| ≤
          2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (2 * T.blockIndex)) ∧
      ∀ (η : StepVariable (finiteCells F)) (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions),
        (∀ b, ‖η b‖ < T.ballRadius) → AreUnitVectors X → bondListDistance Y c ≤ T.blockIndex →
        |bondDeriv (cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y η) V c X -
          bondDeriv (cellCentredExpansion true T.a T.chainParams.ρA (frameRadius x) f Y 0) (uniformField F F.top) c X| ≤
          2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (2 * T.blockIndex)
def CentredExpansionNearUniformTop : Prop :=
  EventuallyInParameters fun T => ∃ R : ℕ, 4 * R + 8 ≤ T.n₀ ∧ CentredExpansionNearUniformTopAt T R
end YangMills.Construction.ColdStepAtMirrorFrames
end
