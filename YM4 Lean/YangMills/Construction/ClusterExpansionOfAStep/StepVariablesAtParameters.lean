import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ColdStepAtMirrorFrames
namespace RenormalizationStepParameters.ParameterAssignment
variable (T : ParameterAssignment)
def Compatible (c : ColdChainParameters) : Prop :=
  c.δ₁ = T.δ₁ ∧ c.lam = T.lam ∧ c.ρA = T.ρA ∧ c.σA = T.σA ∧ c.cg = T.cg ∧ c.N = T.N ∧ c.δ₂ = T.δc ∧
    c.Admissible T.coupling T.side
def stepParamsAt (c : ColdChainParameters) (k : ℕ) (y : ℝ) : StepParameters :=
  ⟨T.coupling, T.side, c, T.Ct, T.rt, T.η₃, k, T.threshold, T.cutoff, T.Cs, T.E, T.n₀, T.CE, y⟩
def HoldsFrom (P : StepParameters → Prop) : Prop :=
  ∃ (c : ColdChainParameters) (k : ℕ), T.Compatible c ∧ ∀ y : ℝ, T.yC ≤ y → P (T.stepParamsAt c k y)
end RenormalizationStepParameters.ParameterAssignment
end YangMills.Construction
end
