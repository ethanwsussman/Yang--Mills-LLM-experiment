import YangMills.Construction.ColdChainAtEveryLevel.PinnedRelativeGauge
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def criticalFieldChartStatement : Prop :=
  ∀ a θ δ Ca : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < Ca →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ C₁ : ℝ, 0 < C₁ → ∃ σ N₀ : ℝ, 0 < σ ∧ 0 < N₀ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ σ → IsCold S F.top s V →
          ∀ U : ChainChart F, IsCriticalChainOverTop a θ δ Ca C₁ s S V V U →
            ∃ (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (γ : F.Site F.depth → UnitQuaternion),
              (∀ b, b ∉ chordBonds S → w b.1 b.2 = 0) ∧ (∀ b ∈ chordBonds S, ‖w b.1 b.2‖ ≤ N₀ * s) ∧
              AgreeOnBonds S F.depth (chartedField w V)
                (gaugeTransform γ (chartField (referenceFieldChain S V) U F.depth)) ∧
              blockEnergy a S F.depth (chartedField w V) V ≤ chartAction a S (referenceFieldChain S V) U V ∧
              ∀ z ∈ S, γ (cellCentre F.depth z) = chartGauge (referenceFieldChain S V) U F.top z
end YangMills.Construction.BlockAverages
end
