import YangMills.Construction.ColdChainAtEveryLevel.PinnedRelativeGauge
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def pinnedGaugeAtGoodCellStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ : ℝ, 0 < C₁ →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ c → ∃ σ : ℝ, 0 < σ ∧
        ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
          IsOrthantRegular S m →
          ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions), 0 < s → s ≤ σ →
            IsCold S F.top s V →
            (∀ y i, ‖v y i‖ ≤ s) →
            ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V (rotatedField v V) U →
              ∀ (X : F.FieldChain) (k : F.SiteGauge) (z : F.Cell), X F.top = rotatedField v V → z ∈ S →
                patchAction a S z X k ≤ ε ^ 2 →
                ∃ Γ : F.SiteGauge,
                  IsPinnedGauge a C S z (chartChain (referenceFieldChain S V) U (rotatedField v V))
                    (chartGauge (referenceFieldChain S V) U) X k Γ ∧
                  relativeEnergy a S z (chartChain (referenceFieldChain S V) U (rotatedField v V))
                    (chartGauge (referenceFieldChain S V) U) X k Γ ≤ Cd * ε ^ 2
end YangMills.Construction.BlockAverages
end
