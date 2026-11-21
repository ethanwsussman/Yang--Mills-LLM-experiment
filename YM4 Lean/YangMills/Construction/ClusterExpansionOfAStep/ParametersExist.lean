import YangMills.Construction.ClusterExpansionOfAStep.StepVariablesAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
def ParametersCanBeChosen : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (cK κ δ₁ : ℝ) (J₀ : ℕ), ∀ P : ColdStepAtMirrorFrames.StepParameters → Prop,
    ColdStepAtMirrorFrames.EventuallyInParameters P →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
      ∀ (C₀ : ℝ) (ceilRate : RenormalizationStepParameters.ChainParameters → ℝ) (ceilThreshold : RenormalizationStepParameters.ChainParameters → ℝ → ℝ)
        (floorN : RenormalizationStepParameters.ChainParameters → ℝ → ℝ → ℕ) (floorCs : RenormalizationStepParameters.ChainParameters → ℝ → ℝ → ℝ)
        (floorK : ℕ → ℝ),
        (∀ D, 0 < ceilRate D) → (∀ D r, 0 < ceilThreshold D r) →
        ∃ T : RenormalizationStepParameters.ParameterAssignment, T.coupling = a ∧ T.coercivity = cK ∧ T.κ = κ ∧ T.δ₁ = δ₁ ∧
          T.baseDepth = J₀ ∧ T.side = L ∧
          C₀ ≤ T.derivBound ∧ T.rt ≤ ceilRate T.toChainParameters ∧
          T.threshold ≤ ceilThreshold T.toChainParameters T.rt ∧
          floorN T.toChainParameters T.rt T.threshold ≤ T.n₀ ∧
          floorCs T.toChainParameters T.rt T.threshold ≤ T.Cs ∧
          (∀ k, floorK k ≤ T.N k) ∧ T.Admissible ∧ T.HoldsFrom P
end ClusterExpansionOfAStep
end YangMills.Construction
end
