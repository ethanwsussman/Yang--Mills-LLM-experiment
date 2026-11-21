import YangMills.Construction.ColdChainAtEveryLevel.VariationsOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def chartFitSecondVariationStatement : Prop :=
  ∀ L : ℕ, Odd L → 5 ≤ L → ∃ C ρ₀ σ₀ : ℝ, 0 < C ∧ 0 < ρ₀ ∧ 0 < σ₀ ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (ρ σ : ℝ) (V : F.GaugeField F.top) (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions),
        0 < ρ → ρ ≤ ρ₀ → 0 < σ → σ ≤ σ₀ →
        IsCold S F.top σ V → SupportedOnChords S w → SupportedOnChords S dw →
        (∀ b ∈ chordBonds S, ‖w b.1 b.2‖ ≤ ρ) →
        IsCold S F.depth σ (chartedField w V) → ∀ c ∈ innerBonds S F.top,
        AnalyticAt ℝ (fun τ : ℝ => blockFit (chartedField (chartLineShift w dw τ) V) V c) 0 ∧
        ‖bondContourVariation (chartedField w V) dw c‖ ^ 2 -
            C * (ρ + σ) * chordSqNormOnPair S c.1 (c.1 + unitStep F.top c.2) dw ≤
          deriv (deriv fun τ : ℝ => blockFit (chartedField (chartLineShift w dw τ) V) V c) 0
end YangMills.Construction.BlockAverages
end
