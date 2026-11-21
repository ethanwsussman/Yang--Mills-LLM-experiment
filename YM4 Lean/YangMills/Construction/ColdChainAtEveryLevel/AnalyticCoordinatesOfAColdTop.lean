import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def analyticChartCoordsStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ (σ : ℝ) (N : ℕ → ℝ), 0 < σ ∧ (∀ k, 0 < N k) ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ σ → IsCold S F.top s V →
          HasRegularCoordinates a δ ρ N S V ∧
          ∀ (F' : BlockFrame) (S' : Finset F'.Cell) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell)
            (r : ℕ), F'.blockSide = L → F'.depth = F.depth → IsAdmissibleAmbient F' → IsOrthantRegular S' m →
            IsCold S' F'.top s V' →
            AgreeOnBall S V S' V' Y Y' r → HasComparableCoordinates a δ ρ s N S V S' V' Y Y' r
end YangMills.Construction.BlockAverages
end
