import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExponentsOfTheStep
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionsInTheLawAtATop
import YangMills.Construction.SummableBoundsOfTheFlow.TheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.TransportAtSixDerivatives
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.LawAtTop
structure LawAtTopHypotheses (T : ColdStepAtMirrorFrames.StepParameters) (Cq Cz : ℕ → ℝ)
    (Cr : ℕ → ℕ → ℕ → ℝ) (C : ℝ) (Ck : ℕ → ℝ) : Prop where
  ordered : T.IsOrdered
  two_le : 2 ≤ T.n₀
  one_le_coupling : 1 ≤ T.coupling
  one_le_Cs : 1 ≤ T.Cs
  frames : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → Interpolation.InterpolatedFrameBoundsAt T Cq Cz Cr t x
  transport : Interpolation.TransportBoundsAt T C Ck
  exponents : ColdStepAtMirrorFrames.CellExponentsBoundedAt T
def lawAtTopFromInterpolatedFrames : Prop :=
  ∀ (T : ColdStepAtMirrorFrames.StepParameters) (Cq Cz : ℕ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) (C : ℝ) (Ck : ℕ → ℝ),
    LawAtTopHypotheses T Cq Cz Cr C Ck → ∀ (t : ℕ) (x ε : ℝ) (φ h : ColdStepAtMirrorFrames.LocalFamily)
    (star : Bool) (F : BlockAverages.BlockFrame) (V : F.GaugeField F.top), T.coupling ≤ x → 0 < ε →
    FamilyNorms.IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E (T.E / T.η₃) φ →
    FamilyNorms.IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε (ε / T.η₃) h →
    ColdStepAtMirrorFrames.IsCubicTopTorus T.L t T.n₀ F →
    ColdStepAtMirrorFrames.IsSmallCurvature (5 / 4 * T.σ) V →
    LawAtTop star T.a T.chainParams.ρA x (ColdStepAtMirrorFrames.frameRadius x) (T.σ / 64)
      T.chainParams.lam T.κ (T.Cs * (ε / T.η₃) * x ^ (-(1 / 2 : ℝ))) (T.Cs * (1 + T.E / T.η₃)) T.p
      (fun q => |Cz q|) (4 * T.L ^ 4) (1 + (BlockAverages.centredCube T.L).card) φ h V ∧
    ∀ b : ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F)),
      ColdStepAtMirrorFrames.ballExpectation (ColdStepAtMirrorFrames.cutoffFactor (T.σ / 64) T.p)
        (fun η => exponentSum star T.a T.chainParams.ρA x (ColdStepAtMirrorFrames.frameRadius x) φ η V)
        (fun η => ‖η b‖ ^ 2) ≤ Cq 1 * x⁻¹
end YangMills.Construction.LawAtTop
end
