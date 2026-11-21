import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChainNoise
def existsNoiseRuleStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters), ℓ.Admissible → ∀ T : WeightedResponses.StageTower ℓ,
    ∃ rule : ChainNoise.NoiseRule ℓ, rule.IsAdmissible T
end YangMills.Construction.ChainNoise
end
