import YangMills.Construction.ColdStepAtMirrorFrames.AxialRotationsOfATop
import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.ResponseInTheExpansion.ExpansionOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ResponseInTheExpansion
variable {F : BlockFrame}
def NearUniformTopResponse (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x →
    LinearResponse.IsRegularOnTorus T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f F →
    IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → ∀ sign : Bool,
      (∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ < T.ballRadius) →
        |cellCentredExpansion sign T.a T.chainParams.ρA (frameRadius x) f Y η V| ≤
          2⁻¹ ^ 8 * T.E / torusDecayFactor T.L T.decayRate T.blockIndex) ∧
      (∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (c : Fin 1 → F.Site F.top × Fin 4)
        (X : Fin 1 → imaginaryQuaternions),
        (∀ b, ‖η b‖ < T.ballRadius) → AreUnitVectors X → bondListDistance Y c ≤ T.blockIndex →
        |bondDeriv (cellCentredExpansion sign T.a T.chainParams.ρA (frameRadius x) f Y η) V c X| ≤
          2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (2 * T.blockIndex)) ∧
      ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (c : Fin 2 → F.Site F.top × Fin 4)
        (X : Fin 2 → imaginaryQuaternions),
        (∀ b, ‖η b‖ < T.ballRadius) → AreUnitVectors X → bondListDistance Y c ≤ T.blockIndex →
        |bondDeriv (cellCentredExpansion sign T.a T.chainParams.ρA (frameRadius x) f Y η) V c X -
          bondDeriv (cellCentredExpansion true T.a T.chainParams.ρA (frameRadius x) f Y 0) (flatTopField (F := F)) c
            (axialGaugeRotated V Y c X)| ≤ 2⁻¹ ^ 10 * T.E / torusDecayFactor T.L T.decayRate (2 * T.blockIndex)
def nearUniformTopResponseStatement : Prop := EventuallyInParameters NearUniformTopResponse
end ResponseInTheExpansion
end YangMills.Construction
end
