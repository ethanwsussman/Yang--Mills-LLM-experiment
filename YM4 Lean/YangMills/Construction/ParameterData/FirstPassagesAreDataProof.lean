import YangMills.Construction.QuaternionicWilsonModel.TheTopOfTheTrajectoryWithTheFlowProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
open TorusLumps RenormalizationStepParameters SequencePassage
private theorem firstPassageIndex_unique {B g : ℝ} {x : ℕ → ℝ} {K K' : ℕ}
    (h : IsFirstPassageIndex B g x K) (h' : IsFirstPassageIndex B g x K') : K' = K := by apply _root_.YangMills.SharedProofs.p30851 <;> assumption
theorem windowMembersAreData (hP : firstPassageExistsStatement) : windowMembersAreDataStatement := by
  intro T y D hD g hg hy K β hK hβ
  have hW : passageThreshold D.shift g ≤ β ∧ IsFirstPassageIndex D.shift g (D.coupling β) K := hβ
  obtain ⟨hbare, hcut⟩ := hW
  obtain ⟨K', hpass⟩ := hP T y D hD g hg hy β hbare
  obtain rfl : K' = K := firstPassageIndex_unique hcut hpass.isFirstPassageIndex
  have hX : D.X₀ ≤ g ^ (-2 : ℤ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hyX : y ≤ D.X₀ := hD.errorMargin.floor_le
  have hfloor : ∀ j ≤ K', D.X₀ ≤ D.coupling β j := fun j hj => hX.trans (hpass.coupling_gt j hj).le
  refine
    { two_le := hK
      coupling_ge := hyX.trans hX
      threshold_le := hbare
      passage := hcut
      floor := fun j hj => hyX.trans (hfloor j hj)
      floor_bound := hfloor
      le_threshold := hcut.1
      room := ?_ }
  have hBs := hD.shift_ge
  show y + 2 * T.B ≤ g ^ (-2 : ℤ) + D.shift
  linarith
end YangMills.Construction.TrajectoryData
end
