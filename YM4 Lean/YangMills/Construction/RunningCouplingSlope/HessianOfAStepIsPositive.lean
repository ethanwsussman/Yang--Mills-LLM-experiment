import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open BlockAverages RenormalizationStepParameters TorusFields ReferenceDensity
def stepHessianPosDefStatement : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ (t n : ℕ) [NeZero n] (V : TorusField n), 64 ≤ n → IsCold (9 / 8 * T.threshold) V →
    (chartedHessian (F := torusFrame T.side t n) T.coupling T.ρA
      (readAtLevel (torusFrame T.side t n) (torusFrame T.side t n).top V) 0).PosDef
end RunningCouplingSlope
end YangMills.Construction
end
