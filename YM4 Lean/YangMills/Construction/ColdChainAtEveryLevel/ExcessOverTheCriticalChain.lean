import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainIsLeast
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def criticalChainExcessStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ : ℝ, 0 < C₁ →
      ∃ C : ℝ, 0 < C ∧ ∃ ε σ c : ℝ, 0 < ε ∧ 0 < σ ∧ 0 < c ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s → s ≤ σ →
          IsCold S F.top s V →
          (∀ y i, ‖v y i‖ ≤ s) →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V (rotatedField v V) U →
            ∀ (X : F.FieldChain) (k : F.SiteGauge), X F.top = rotatedField v V →
              ∃ Γ : F.Cell → F.SiteGauge,
                (∀ z ∈ cellsFarFromHighEnergy a ε S X k, IsPinnedGauge a C S z
                  (chartChain (referenceFieldChain S V) U (rotatedField v V))
                  (chartGauge (referenceFieldChain S V) U) X k (Γ z)) ∧
                c * ((highEnergyCells a ε S X k).card + ∑ z ∈ cellsFarFromHighEnergy a ε S X k,
                  relativeEnergy a S z (chartChain (referenceFieldChain S V) U (rotatedField v V))
                    (chartGauge (referenceFieldChain S V) U) X k (Γ z)) ≤
                gaugedChainAction a S X k - chartAction a S (referenceFieldChain S V) U (rotatedField v V)
end YangMills.Construction.BlockAverages
end
