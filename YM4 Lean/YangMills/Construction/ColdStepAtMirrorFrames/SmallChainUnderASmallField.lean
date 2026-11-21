import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def SmallMinimizingChainExists : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∀ L : ℕ, Odd L → ∀ c : ColdChainParameters, c.Admissible a L → ∀ F : BlockFrame,
    F.blockSide = L → IsLargeCubicTorus F →
    ∀ k : ℕ, k ≤ F.top → ∃ C m₀ : ℝ, 1 ≤ C ∧ 0 < m₀ ∧ ∀ m : ℝ, 0 < m → m ≤ m₀ → ∀ Y : F.GaugeField k,
      (∀ x i, ‖(Y x i : ℍ[ℝ]) - 1‖ ≤ m) → ∃ Z : F.FieldChain, Z k = Y ∧
        (∀ j, j ≤ k → ∀ x i, ‖(Z j x i : ℍ[ℝ]) - 1‖ ≤ C * m) ∧
        wilsonAction (finiteCells F) (Z 0) + a * ∑ j ∈ Finset.range k, ∑ b ∈ innerBonds (finiteCells F) (j + 1),
          blockFit (Z j) (Z (j + 1)) b = minimalAction a (finiteCells F) k Y
end YangMills.Construction.ColdStepAtMirrorFrames
end
