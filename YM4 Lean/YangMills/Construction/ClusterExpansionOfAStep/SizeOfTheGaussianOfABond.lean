import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open StepSettings ColdStepAtMirrorFrames
def GaussianLogMassLeLog : Prop :=
  ∀ (lam ρ : ℝ) (p : ℝ → ℝ), 0 < lam → 0 < ρ → IsCutoff ρ p → ∃ C y₀ : ℝ, 0 < C ∧
    ∀ R : StepSetup, R.ballRadius = ρ → R.barrierFn = p → y₀ ≤ R.coupling →
      |R.gaussianLogMass lam| ≤ C * Real.log R.coupling
end YangMills.Construction.ClusterExpansionOfAStep
end
