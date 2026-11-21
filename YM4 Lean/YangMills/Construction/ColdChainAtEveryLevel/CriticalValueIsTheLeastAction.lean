import YangMills.Construction.ColdChainAtEveryLevel.PinnedRelativeGauge
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def criticalValueEqMinimalActionStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ : ℝ, 0 < C₁ → ∃ σ : ℝ, 0 < σ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s → s ≤ σ →
          IsCold S F.top s V →
          (∀ y i, ‖v y i‖ ≤ s) →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V (rotatedField v V) U →
            minimalAction a S F.top (rotatedField v V) =
                chartAction a S (referenceFieldChain S V) U (rotatedField v V) ∧
            ∀ (X : F.FieldChain) (k : F.SiteGauge), X F.top = rotatedField v V →
              chartAction a S (referenceFieldChain S V) U (rotatedField v V) ≤ gaugedChainAction a S X k
end YangMills.Construction.BlockAverages
end
