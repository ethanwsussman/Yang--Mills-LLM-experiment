import YangMills.Construction.Torus.BoundsOnTheCompressedOperatorsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Finset
noncomputable section
namespace YangMills.Construction.GeneralTorus.NeumannSeriesProof
section Matrices
variable {Y : Type} [Fintype Y] [DecidableEq Y]
theorem abs_one_apply_le (c c' : Y) : |(1 : Matrix Y Y ℝ) c c'| ≤ (1 : Matrix Y Y ℝ) c c' := by
  by_cases h : c = c'
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]
end Matrices
section Preliminaries
variable {Y : Type} [Fintype Y] [DecidableEq Y]
end Preliminaries
section Core
variable {Y : Type} [Fintype Y] [DecidableEq Y]
end Core
theorem coarseSpacing_pos {W : GaugeSetting} (c : W.CoarseBond) : 0 < GaugeSetting.coarseSpacing c := by apply _root_.YangMills.Construction.GeneralTorus.CompressedBoundsProof.coarseSpacing_pos <;> assumption
end YangMills.Construction.GeneralTorus.NeumannSeriesProof
end
