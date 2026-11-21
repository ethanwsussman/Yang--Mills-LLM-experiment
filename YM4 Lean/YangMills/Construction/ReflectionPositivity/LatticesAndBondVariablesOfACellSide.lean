import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.Chessboard
def IsCellSideOf (L : ℕ) (side : ℝ) : Prop := ∃ i : ℕ, side = (L : ℝ) ^ i
end YangMills.Construction.ReflectionPositivity.Chessboard
