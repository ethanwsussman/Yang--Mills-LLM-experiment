import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def ExpansionAtFrameLocalityAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → ∀ star : Bool,
      ∀ (F' : BlockFrame) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r k : ℕ)
        (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
        IsCubicTopTorus T.L t T.n₀ F' → IsSmallCurvature (5 / 4 * T.σ) V' →
        AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r → T.blockIndex ≤ r → k ≤ 2 →
        (∀ l, BondWithinRadius r (h l)) → AreUnitVectors X →
        |bondDeriv (cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y 0) V (bondsAt Y h) X -
          bondDeriv (cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y' 0) V' (bondsAt Y' h) X| ≤
          2⁻¹ ^ 8 * T.E / torusDecayFactor T.L T.decayRate r
def ExpansionAtFrameLocality : Prop := EventuallyInParameters ExpansionAtFrameLocalityAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
