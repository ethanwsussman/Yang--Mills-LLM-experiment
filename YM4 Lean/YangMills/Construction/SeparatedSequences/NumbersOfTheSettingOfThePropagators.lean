import YangMills.Construction.SeparatedSequences.BlockFloorOfThePositivityOfTheOperator
import YangMills.Construction.SeparatedSequences.NumbersOfTheThreeSystems
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences
def propagatorGapFloor (L : ℕ) : ℝ :=
  max (InputConstants.gapLength L : ℝ) (64 * (4 * Real.log L + Real.log 2) / blockOperatorRate L)
def propagatorScaleBound (L : ℕ) : ℝ :=
  max (32 * (L : ℝ) ^ 2 * (InputConstants.gapMultiplier L : ℝ) * (InputConstants.blockPow L : ℝ))
    (max (treeBlockLower L)
      (max (positiveDefiniteBlockSizeFloor L)
        (max (ThreeSystemConstants.pairedBlockLower L)
          ((2 * treeWalkConst L * (treeExpansionTreeWalkCount L : ℝ)) ^ 2))))
def IsPowerAboveScaleBound (L m : ℕ) : Prop :=
  (∃ n : ℕ, m = L ^ n) ∧ propagatorScaleBound L ≤ (m : ℝ)
def propagatorScaleFloor (L : ℕ) : ℕ := sInf {m | IsPowerAboveScaleBound L m}
end YangMills.Construction.SeparatedSequences
end
