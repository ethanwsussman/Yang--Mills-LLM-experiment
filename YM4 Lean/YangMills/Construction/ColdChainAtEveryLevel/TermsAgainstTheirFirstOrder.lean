import YangMills.Construction.ColdChainAtEveryLevel.TermsAndVariationsOfAFramedChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def termwiseFirstVariationStatement : Prop :=
  ∀ a θ del Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < del → del ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ C Cd : ℝ, 0 < C₁ → 0 < C → 0 < Cd →
      ∃ C₂ c : ℝ, 0 < C₂ ∧ 0 < c ∧ ∀ e0 : ℝ, 0 < e0 → e0 ≤ c → ∃ σ : ℝ, 0 < σ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s → s ≤ σ →
          IsCold S F.top s V →
          (∀ y i, ‖v y i‖ ≤ s) →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ del Ca C₁ s S V (rotatedField v V) U →
            ∀ (X : F.FieldChain) (k Γ : F.SiteGauge) (z : F.Cell), X F.top = rotatedField v V → z ∈ S →
              patchAction a S z X k ≤ e0 ^ 2 →
              HasPinnedGaugeAt a C Cd e0 S z (criticalFieldChain S V v U) (criticalGauge S V U) X k Γ →
              ∃ err : F.ActionTerm → ℝ,
                (∀ t ∈ patchActionTerms S z,
                  firstVariation a (criticalFieldChain S V v U) (criticalGauge S V U)
                      (gaugeVariation (criticalFieldChain S V v U) (criticalGauge S V U) X k Γ) t +
                    (1 / 32) * relativeEnergyDensity a (criticalFieldChain S V v U) (criticalGauge S V U) X k Γ t
                      - err t ≤
                  actionTermValue a X k t - actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t) ∧
                (∀ t, 0 ≤ err t) ∧
                ∑ t ∈ patchActionTerms S z, err t ≤
                  C₂ * s * relativeEnergy a S z (criticalFieldChain S V v U) (criticalGauge S V U) X k Γ
end YangMills.Construction.BlockAverages
end
