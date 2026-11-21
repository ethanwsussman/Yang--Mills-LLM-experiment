import YangMills.Construction.ParameterData.SlopeAtTheData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
open CouplingFlow RenormalizationStepParameters TorusLumps
private theorem floorStar_le_threshold {T : ParameterAssignment} {y : ℝ} {D : TrajectoryParameters T y}
    (hD : D.Admissible) {g : ℝ} (hg : D.floorStar ≤ g ^ (-2 : ℤ)) : D.X₀ ≤ D.threshold g := by
  have hB : 0 < T.B := hD.errorMargin.admissible.B_pos
  have hs : 2 * T.B ≤ D.shift := hD.shift_ge
  have hX : D.X₀ ≤ D.floorStar := (le_max_left _ _).trans (le_max_left _ _)
  have ht : D.threshold g = g ^ (-2 : ℤ) + D.shift := rfl
  linarith
theorem couplingDecrease : couplingDecreaseStatement := by
  intro T y D hD g _ hg K β hβ i j hij hjK
  obtain ⟨_, _, hk⟩ := hβ
  exact (hD.errorMargin.drop_two_sided β i j hij fun l hl =>
    (floorStar_le_threshold hD hg).trans (hk l (hl.trans_le hjK)).le).1
end YangMills.Construction.TrajectoryData
end
