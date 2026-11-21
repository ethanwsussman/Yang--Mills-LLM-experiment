import YangMills.Construction.ColdChainAtEveryLevel.PinnedRelativeGauge
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def zeroEnergyFramingsAgreeStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ C : ℝ, 0 < C₁ → 0 < C → ∃ σ : ℝ, 0 < σ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F →
        1024 ≤ m → IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ σ → IsCold S F.top s V →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V V U →
            ∀ (X : F.FieldChain) (Γ : F.Cell → F.SiteGauge), X F.top = V →
              (∀ z ∈ S, IsPinnedGauge a C S z (chartChain (referenceFieldChain S V) U V)
                (chartGauge (referenceFieldChain S V) U) X (fun _ _ => 1) (Γ z)) →
              (∀ z ∈ S, relativeEnergy a S z (chartChain (referenceFieldChain S V) U V)
                (chartGauge (referenceFieldChain S V) U) X (fun _ _ => 1) (Γ z) = 0) →
              ∃ γ : F.Site F.depth → UnitQuaternion,
                (∀ z ∈ S, γ (cellCentre F.depth z) = chartGauge (referenceFieldChain S V) U F.top z) ∧
                AgreeOnBonds S F.depth (X F.depth)
                  (gaugeTransform γ (chartField (referenceFieldChain S V) U F.depth))
end YangMills.Construction.BlockAverages
end
