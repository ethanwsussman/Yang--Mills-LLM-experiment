import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.RunningCouplingSlope.ExponentOfAStepAlongACurve
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepSettings LaplaceAsymptotics
namespace RunningCouplingSlope
def stepExponentNearTrivialStatement : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ k : ℕ, ∃ C q : ℝ, 0 < C ∧ 0 ≤ q ∧
    ∀ (y : ℝ) (R : StepSetup), T.floorMin ≤ y → R.OnParameters T y →
      ∀ (n : ℕ) [NeZero n] (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), T.n₀ ≤ n →
        (∀ l, ‖X l‖ ≤ 1) →
        Nonempty ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))) ∧
        (Fintype.card ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))) : ℝ) ≤ C * (n : ℝ) ^ q ∧
        IsAdmissibleExponentFamily T.ballRadius T.lam (C * (n : ℝ) ^ q)
          (chartEnergyAlongCurve R n c X) (exponentRemainderAlongCurve R n c X)
end RunningCouplingSlope
end YangMills.Construction
end
