import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def quadraticResponseAtFlatStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∃ N0 : ℝ, 0 < N0 ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        HasFlatSecondVariation a δ N0 S
end YangMills.Construction.BlockAverages
end
