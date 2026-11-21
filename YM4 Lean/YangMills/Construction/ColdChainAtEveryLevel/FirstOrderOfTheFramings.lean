import YangMills.Construction.ColdChainAtEveryLevel.TermsAndVariationsOfAFramedChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def gluedFirstVariationStatement : Prop :=
  ∀ a θ del Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < del → del ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ C Cd : ℝ, 0 < C₁ → 0 < C → 0 < Cd →
      ∃ C₂ c : ℝ, 0 < C₂ ∧ 0 < c ∧ ∀ e0 : ℝ, 0 < e0 → e0 ≤ c → ∃ σ : ℝ, 0 < σ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s → s ≤ σ →
          IsCold S F.top s V →
          (∀ y i, ‖v y i‖ ≤ s) →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ del Ca C₁ s S V (rotatedField v V) U →
            ∀ (X : F.FieldChain) (k : F.SiteGauge) (Γ : F.Cell → F.SiteGauge), X F.top = rotatedField v V →
              (∀ z ∈ cellsClearOfHighEnergy a e0 S X k,
                HasPinnedGaugeAt a C Cd e0 S z (criticalFieldChain S V v U) (criticalGauge S V U) X k (Γ z)) →
              |∑ z ∈ cellsClearOfHighEnergy a e0 S X k, ∑ t ∈ actionTerms S,
                  cellPartition S (actionTermSite t) z *
                  firstVariation a (criticalFieldChain S V v U) (criticalGauge S V U)
                    (gaugeVariation (criticalFieldChain S V v U) (criticalGauge S V U) X k (Γ z)) t| ≤
                C₂ * s * (∑ z ∈ cellsClearOfHighEnergy a e0 S X k,
                    relativeEnergy a S z (criticalFieldChain S V v U) (criticalGauge S V U) X k (Γ z) +
                  e0 * (S.filter fun y => e0 ^ 2 < patchAction a S y X k).card)
end YangMills.Construction.BlockAverages
end
