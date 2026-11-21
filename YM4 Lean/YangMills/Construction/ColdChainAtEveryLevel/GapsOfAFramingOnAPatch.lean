import YangMills.Construction.ColdChainAtEveryLevel.FramingFromAGaugeOfLevelZero
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def bondMisfitDefect (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k Γ : F.SiteGauge) (j : ℕ)
    (c : F.Site (j + 1) × Fin 4) : UnitQuaternion :=
  bondMisfit (gaugedChainFields X Γ j) (balancedLinkAgainst W kW (gaugedChainFields X Γ) j)
      (framedUpperField W kW X k Γ j) c *
    (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)⁻¹
def framingDefectsOnPatchStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ : ℝ, 0 < C₁ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ c → ∃ σ : ℝ, 0 < σ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s → s ≤ σ →
          IsCold S F.top s V →
          (∀ y i, ‖v y i‖ ≤ s) →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V (rotatedField v V) U →
            ∀ (X : F.FieldChain) (k : F.SiteGauge) (z : F.Cell), X F.top = rotatedField v V → z ∈ S →
              patchAction a S z X k ≤ ε₀ ^ 2 →
              ∀ γ : F.Site 0 → UnitQuaternion,
                quarticDefectNorm S z (criticalFieldChain S V v U) X
                  (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k γ) 0 ≤ c →
                (∀ j, j < F.top → ∀ y ∈ sitesOfCells S (j + 1), baseSite y ∈ patchBaseSites S z →
                  ‖relativePathAverage (gaugedChainFields X
                      (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k γ) j)
                    (criticalFieldChain S V v U j) y - 1‖ ≤ 1 / 2) ∧
                (∀ j, j < F.top →
                  quarticDefectNorm S z (criticalFieldChain S V v U) X
                      (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k γ) j ≤
                    C * (quarticDefectNorm S z (criticalFieldChain S V v U) X
                        (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k γ) 0 + ε₀ + s)) ∧
                (∀ b ∈ patchInnerBonds S z F.top,
                  normSubOne (topDefect (criticalFieldChain S V v U) (criticalGauge S V U) X k
                      (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k γ) b.1 b.2) ≤
                    C * (quarticDefectNorm S z (criticalFieldChain S V v U) X
                        (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k γ) 0 + ε₀ + s)) ∧
                (∀ j, j < F.top → ∑ c ∈ patchInnerBonds S z (j + 1),
                  normSubOne (bondMisfitDefect (criticalFieldChain S V v U) (criticalGauge S V U) X k
                    (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k γ) j c) ^ 2 ≤
                    2 / a * relativeEnergy a S z (criticalFieldChain S V v U) (criticalGauge S V U) X k
                      (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k γ)) ∧
                ∀ j, j < F.top →
                  quarticDefectNorm S z (criticalFieldChain S V v U) X
                      (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k γ) j ≤
                    4 * (quarticDefectNorm S z (criticalFieldChain S V v U) X
                        (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k γ) 0 +
                      Real.sqrt (2 / a * relativeEnergy a S z (criticalFieldChain S V v U) (criticalGauge S V U) X k
                        (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k γ)))
end YangMills.Construction.BlockAverages
end
