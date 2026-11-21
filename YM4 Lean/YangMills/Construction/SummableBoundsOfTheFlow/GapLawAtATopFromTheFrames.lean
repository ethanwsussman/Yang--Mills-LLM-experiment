import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfASlopeAtATop
import YangMills.Construction.SummableBoundsOfTheFlow.PartsBetweenAreSmoothInTheParameters
import YangMills.Construction.SummableBoundsOfTheFlow.TheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.TransportAtSixDerivatives
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.Cumulants
variable {F : BlockAverages.BlockFrame}
structure InterpolatedLawHypotheses (T : ColdStepAtMirrorFrames.StepParameters) (Cq Cz : ℕ → ℝ)
    (Cr : ℕ → ℕ → ℕ → ℝ) (C : ℝ) (Ck : ℕ → ℝ) : Prop where
  ordered : T.IsOrdered
  two_le : 2 ≤ T.n₀
  one_le : 1 ≤ T.coupling
  one_le_Cs : 1 ≤ T.Cs
  frames : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → Interpolation.InterpolatedFrameBoundsAt T Cq Cz Cr t x
  transport : Interpolation.TransportBoundsAt T C Ck
  parts : Interpolation.InterpolatedPartsSmoothAt T
def interpolatedLawAtTopFromFrames : Prop :=
  ∀ (T : ColdStepAtMirrorFrames.StepParameters) (Cq Cz : ℕ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) (C : ℝ) (Ck : ℕ → ℝ),
    InterpolatedLawHypotheses T Cq Cz Cr C Ck → ∀ (t : ℕ) (x s : ℝ) (φ : ColdStepAtMirrorFrames.LocalFamily)
    (F : BlockAverages.BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x → 0 ≤ s → s ≤ 1 →
    FamilyNorms.IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E (T.E / T.η₃) φ →
    ColdStepAtMirrorFrames.IsCubicTopTorus T.L t T.n₀ F →
    ColdStepAtMirrorFrames.IsSmallCurvature (5 / 4 * T.σ) V →
    InterpolatedLawAtTop s T.a T.chainParams.ρA x (ColdStepAtMirrorFrames.frameRadius x) (T.σ / 64)
      T.chainParams.lam T.κ (T.Cs * (1 + T.E / T.η₃)) T.p (fun q => |Cz q|) (4 * T.L ^ 4)
      (1 + (BlockAverages.centredCube T.L).card) φ V ∧
    (∀ η : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells F),
      (∀ b, ‖η b‖ < T.σ / 64) →
      interpolatedExponentOfTerms s T.a T.chainParams.ρA x (ColdStepAtMirrorFrames.frameRadius x) φ η V =
        Interpolation.familyLawExponent s T.a T.chainParams.ρA x (ColdStepAtMirrorFrames.frameRadius x) φ V η) ∧
    ∃ (Φ : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells F) → ℝ)
      (d : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F)) →
        ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F)) → ℝ),
      Interpolation.LawMomentBounds T.ballRadius x T.κ T.Cs T.p Cq Cr d Φ ∧
      ColdStepAtMirrorFrames.ballDensity (ColdStepAtMirrorFrames.cutoffFactor T.ballRadius T.p) Φ =
        ColdStepAtMirrorFrames.ballDensity (ColdStepAtMirrorFrames.cutoffFactor T.ballRadius T.p)
          (fun η => interpolatedExponentOfTerms s T.a T.chainParams.ρA x
            (ColdStepAtMirrorFrames.frameRadius x) φ η V)
end YangMills.Construction.Cumulants
end
