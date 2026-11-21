import YangMills.Construction.ClusterExpansionOfAStep.StepVariablesAtParameters
import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.ResponseInTheExpansion.OneStepToSecondOrder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames RenormalizationStepParameters
namespace ResponseInTheExpansion
def frameHessianCoerciveLocalStatement : Prop :=
  ∀ (T : ParameterAssignment) (c : ColdChainParameters), T.Admissible → T.Compatible c → ∃ C : ℝ, 0 < C ∧
    ∀ (F : BlockFrame) (m : ℕ) (V : F.GaugeField F.top), IsBlockTorus T.side F → 16 ≤ m →
      IsSmallCurvature T.threshold V →
      (frameHessian T.coupling T.ρA m V).IsSymm ∧
      (∀ v : ChartCoordinate F → ℝ, T.lam * ∑ i, v i ^ 2 ≤ ∑ i, v i * (frameHessian T.coupling T.ρA m V).mulVec v i) ∧
      ∀ i j : ChartCoordinate F, |frameHessian T.coupling T.ρA m V i j| ≤ C * Real.exp (-(T.δ₁ * chordBondDist F i.1 j.1))
end ResponseInTheExpansion
end YangMills.Construction
end
