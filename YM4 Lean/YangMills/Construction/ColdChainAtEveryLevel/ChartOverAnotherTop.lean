import YangMills.Construction.ColdChainAtEveryLevel.LocalRestrictionsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.PinnedRelativeGauge
import YangMills.Construction.ColdChainAtEveryLevel.VariationsOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
def criticalChainChartOverTopStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ : ℝ, 0 < C₁ → ∃ σ N₀ : ℝ, 0 < σ ∧ 0 < N₀ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V V' : F.GaugeField F.top), 0 < s → s ≤ σ → IsCold S F.top s V →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V V' U →
            ∃ w : F.Site F.depth → Fin 4 → imaginaryQuaternions, SupportedOnChords S w ∧
              (∀ b ∈ chordBonds S, ‖w b.1 b.2‖ ≤ N₀ * s) ∧
              (∀ b ∈ chordBonds S, expUnit (w b.1 b.2) =
                gaugedBondElement (chartField (referenceFieldChain S V) U F.depth)
                  (chartGauge (referenceFieldChain S V) U F.top) V' b) ∧
              blockEnergy a S F.depth (chartedField w V') V' ≤ chartAction a S (referenceFieldChain S V) U V'
end BlockAverages
end YangMills.Construction
end
