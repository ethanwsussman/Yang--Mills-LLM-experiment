import YangMills.Construction.ColdChainAtEveryLevel.FramingFromAGaugeOfLevelZero
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def topDefectAverageStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ : ℝ, 0 < C₁ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ c →
      ∃ σ : ℝ, 0 < σ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s → s ≤ σ →
          IsCold S F.top s V →
          (∀ y i, ‖v y i‖ ≤ s) →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V (rotatedField v V) U →
            ∀ (X : F.FieldChain) (k : F.SiteGauge) (z : F.Cell), X F.top = rotatedField v V → z ∈ S →
              patchAction a S z X k ≤ ε ^ 2 →
              ∀ g : F.Site 0 → UnitQuaternion,
                quarticDefectNorm S z (criticalFieldChain S V v U) X
                  (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k g) 0 ≤ c →
                ∀ b ∈ patchInnerBonds S z F.top,
                  ‖adjointAction (GaugeMap.frameChange S V z (baseSite b.1))⁻¹
                      (pureComponent ((topDefect (criticalFieldChain S V v U)
                        (criticalGauge S V U) X k
                        (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k g) b.1 b.2 :
                          UnitQuaternion) : ℍ[ℝ])) -
                      iteratedBlockAverage (framedPureDefect S V z (criticalFieldChain S V v U) X
                        (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k g) 0)
                        F.top b.1 b.2‖ ≤
                    4 * Real.sqrt (relativeEnergy a S z (criticalFieldChain S V v U) (criticalGauge S V U) X k
                        (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k g) / a) +
                      C * (quarticDefectNorm S z (criticalFieldChain S V v U) X
                          (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k g) 0 + s +
                        Real.sqrt (relativeEnergy a S z (criticalFieldChain S V v U) (criticalGauge S V U) X k
                          (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k g))) *
                      (quarticDefectNorm S z (criticalFieldChain S V v U) X
                          (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k g) 0 +
                        Real.sqrt (relativeEnergy a S z (criticalFieldChain S V v U) (criticalGauge S V U) X k
                          (pinnedGaugeOfBase (criticalFieldChain S V v U) (criticalGauge S V U) X k g)))
end YangMills.Construction.BlockAverages
end
