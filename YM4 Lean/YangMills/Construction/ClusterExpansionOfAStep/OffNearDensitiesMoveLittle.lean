import YangMills.Construction.ClusterExpansionOfAStep.NearAClassOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
open BlockAverages LumpContours TorusFields TorusLumps RenormalizationStepParameters
def farBlockDensityVariationBound : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ CE y₀ : ℝ, 0 < CE ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ (s : ChartSetting R n) (c : SettingCore R n), s.IsAdmissible → s.IsCoreOf c →
      ∀ 𝒦 ⊆ s.storedComponents c,
        ∀ ζ : s.freeNear (blocksNear R.params.side R.range (𝒦.biUnion id)) → EuclideanSpace ℝ (Fin 3),
          s.InBalls (s.extendByZero (blocksNear R.params.side R.range (𝒦.biUnion id)) ζ) →
          ∑ Y ∈ Finset.univ \ blocksNear R.params.side R.range (𝒦.biUnion id),
              |s.blockDensity (s.field (s.extendByZero (blocksNear R.params.side R.range (𝒦.biUnion id)) ζ)) Y -
                s.blockDensity (s.field 0) Y| +
            ∑ Y ∈ Finset.univ \ blocksNear R.params.side R.range (𝒦.biUnion id),
              |s.logJacobian (s.field (s.extendByZero (blocksNear R.params.side R.range (𝒦.biUnion id)) ζ))
                  (s.extendByZero (blocksNear R.params.side R.range (𝒦.biUnion id)) ζ) Y - s.logJacobian (s.field 0) 0 Y| ≤
            CE * (R.range : ℝ) ^ 4 * Real.log R.coupling * ((blocksNear R.params.side R.range (𝒦.biUnion id)).card : ℝ)
end YangMills.Construction.StepSettings
end
