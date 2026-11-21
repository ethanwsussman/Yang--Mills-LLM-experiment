import YangMills.Construction.ColdChainAtEveryLevel.LocalRestrictionsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.PinnedRelativeGauge
import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def minimizerEqCriticalChainChartStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ ρ : ℝ, 0 < C₁ → 0 < ρ → ρ ≤ 1 →
      ∃ σ N₀ : ℝ, 0 < σ ∧ 0 < N₀ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions),
          0 < s → s ≤ σ → IsCold S F.top s V →
          (∀ y i, ‖v y i‖ ≤ s) → IsCold S F.top s (rotatedField v V) →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V (rotatedField v V) U →
            (∀ b ∈ chordBonds S, minimizingBondCoordinate a ρ S b (rotatedField v V) =
                bondChartCoord (referenceFieldChain S V) V b U v ∧
                ‖minimizingBondCoordinate a ρ S b (rotatedField v V)‖ ≤ N₀ * s) ∧
              ∀ b, b ∉ chordBonds S → minimizingBondCoordinate a ρ S b (rotatedField v V) = 0
end YangMills.Construction.BlockAverages
end
