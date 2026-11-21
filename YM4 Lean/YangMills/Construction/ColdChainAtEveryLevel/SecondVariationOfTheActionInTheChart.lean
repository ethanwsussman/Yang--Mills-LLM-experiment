import YangMills.Construction.ColdChainAtEveryLevel.VariationsOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def chartActionSecondVariationStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ ca : ℝ, 0 < ca ∧ ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∃ C ρ₀ σ₀ : ℝ, 0 < C ∧ 0 < ρ₀ ∧ 0 < σ₀ ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (ρ σ : ℝ) (V : F.GaugeField F.top) (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions),
        0 < ρ → ρ ≤ ρ₀ → 0 < σ → σ ≤ σ₀ →
        IsCold S F.top σ V → SupportedOnChords S w → SupportedOnChords S dw →
        (∀ b ∈ chordBonds S, ‖w b.1 b.2‖ ≤ ρ) →
        IsCold S F.depth σ (chartedField w V) →
        AnalyticAt ℝ (fun τ : ℝ => minimalAction a S F.depth (chartedField (chartLineShift w dw τ) V)) 0 ∧
        ca * ∑ p ∈ innerPlaquettes S F.depth, ‖variationCurl (chartedField w V) dw p‖ ^ 2 -
            C * (ρ + σ) * chordSqNorm S dw ≤
          deriv (deriv fun τ : ℝ => minimalAction a S F.depth (chartedField (chartLineShift w dw τ) V)) 0
end YangMills.Construction.BlockAverages
end
