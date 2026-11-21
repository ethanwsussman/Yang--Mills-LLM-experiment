import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.ResponseInTheExpansion.ExpansionOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FrameLocality
def frameFamilyLocalAt (T : ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : ColdStepAtMirrorFrames.LocalFamily) (F : BlockAverages.BlockFrame) (V : F.GaugeField F.top),
    T.coupling ≤ x →
    LinearResponse.IsRegularOnTorus T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f F →
    ColdStepAtMirrorFrames.IsCubicTopTorus T.L t T.n₀ F →
    ColdStepAtMirrorFrames.IsSmallCurvature (5 / 4 * T.σ) V → ∀ star : Bool,
      ∀ (V' : F.GaugeField F.top) (Y : F.Cell) (r k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4)
        (X : Fin k → BlockAverages.imaginaryQuaternions),
        ColdStepAtMirrorFrames.IsSmallCurvature (5 / 4 * T.σ) V' →
        BlockAverages.AgreeOnBall (ColdStepAtMirrorFrames.finiteCells F) V
          (ColdStepAtMirrorFrames.finiteCells F) V' Y Y r →
        T.blockIndex ≤ r → k ≤ 2 →
        (∀ l, BlockAverages.BondWithinRadius r (h l)) → BlockAverages.AreUnitVectors X →
        |ColdStepAtMirrorFrames.bondDeriv
            (ColdStepAtMirrorFrames.cellCentredExpansion star T.a T.chainParams.ρA
              (ColdStepAtMirrorFrames.frameRadius x) f Y 0) V (ColdStepAtMirrorFrames.bondsAt Y h) X -
          ColdStepAtMirrorFrames.bondDeriv
            (ColdStepAtMirrorFrames.cellCentredExpansion star T.a T.chainParams.ρA
              (ColdStepAtMirrorFrames.frameRadius x) f Y 0) V' (ColdStepAtMirrorFrames.bondsAt Y h) X| ≤
          2⁻¹ ^ 8 * T.E / BlockAverages.torusDecayFactor T.L T.decayRate r
def frameFamilyLocalStatement : Prop :=
  ColdStepAtMirrorFrames.EventuallyInParameters frameFamilyLocalAt
end YangMills.Construction.FrameLocality
end
