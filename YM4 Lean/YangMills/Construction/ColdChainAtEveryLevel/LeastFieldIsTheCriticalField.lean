import YangMills.Construction.ColdChainAtEveryLevel.PinnedRelativeGauge
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def minimalFieldIsCriticalStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ : ℝ, 0 < C₁ → ∃ σ : ℝ, 0 < σ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ σ → IsCold S F.top s V →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V V U →
            ∀ W' : F.GaugeField F.depth,
              (∀ W'' : F.GaugeField F.depth, blockEnergy a S F.depth W' V ≤ blockEnergy a S F.depth W'' V) →
              ∃ γ : F.Site F.depth → UnitQuaternion,
                (∀ z ∈ S, γ (cellCentre F.depth z) = chartGauge (referenceFieldChain S V) U F.top z) ∧
                AgreeOnBonds S F.depth W' (gaugeTransform γ (chartField (referenceFieldChain S V) U F.depth))
end YangMills.Construction.BlockAverages
end
