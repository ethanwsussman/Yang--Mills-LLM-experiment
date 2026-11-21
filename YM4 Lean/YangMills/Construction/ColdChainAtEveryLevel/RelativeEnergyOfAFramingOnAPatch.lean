import YangMills.Construction.ColdChainAtEveryLevel.FramingFromAGaugeOfLevelZero
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def pinnedGaugeRelativeEnergyStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ : ℝ, 0 < C₁ → ∃ c : ℝ, 0 < c ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ c →
      ∃ σ : ℝ, 0 < σ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s → s ≤ σ →
          IsCold S F.top s V →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V (rotatedField v V) U →
            ∀ (X : F.FieldChain) (k : F.SiteGauge) (z : F.Cell), z ∈ S → patchAction a S z X k ≤ ε₀ ^ 2 →
              ∀ γ : F.Site 0 → UnitQuaternion,
                relativeEnergy a S z (criticalFieldChain S V v U) (criticalGauge S V U) X k
                  (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k γ) ≤ 16 * ε₀ ^ 2
end YangMills.Construction.BlockAverages
end
