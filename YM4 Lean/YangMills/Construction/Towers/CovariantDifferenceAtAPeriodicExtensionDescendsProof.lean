import YangMills.Construction.Towers.CovariantDifferenceAtAPeriodicExtensionDescends
import YangMills.Construction.Towers.CovariantDifferenceIsLocalWithACounterpart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels.CovDiffAtLift
open Periodisation Tower
theorem holds (hLoc : Periodisation.LocalLinearMapsPeriodize)
    (hDiff : CovDiffLocality.CovDiffIsLocal) : Claim := by
  intro L hL k n hn j h V hV
  have hL13 : 13 ≤ L := hL.2
  have hOneLe : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hMeshNonneg : 0 ≤ meshAt L k j := zpow_nonneg (by linarith) _
  have hMeshLe : meshAt L k j ≤ 1 := zpow_le_one_of_nonpos₀ hOneLe (by omega)
  have hSideNat : 2 < periodSide L n := by
    have hPow : L ≤ L ^ n := Nat.le_self_pow (by omega) L
    unfold periodSide
    omega
  have hSide : 2 * meshAt L k j < (periodSide L n : ℝ) := by
    have : (2 : ℝ) < (periodSide L n : ℝ) := by exact_mod_cast hSideNat
    linarith
  obtain ⟨T, m, hT, hRest⟩ := hLoc L hL k n hn (CellClass.vertexClass k j h)
    (CellClass.edgeClass k j h) (by simp [CellClass.vertexClass]) (by simp [CellClass.edgeClass])
    (meshAt L k j) hMeshNonneg hSide _ _ (hDiff L hL k n hn j h V hV)
  unfold CovDiffDescends Periodizes
  exact ⟨T, m, fun a b hFar => hT a b fun hNear => hFar (hNear.trans (by linarith)), hRest⟩
end YangMills.Construction.LocalKernels.CovDiffAtLift
end
