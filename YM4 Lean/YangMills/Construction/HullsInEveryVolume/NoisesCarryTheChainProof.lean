import YangMills.Construction.HullsInEveryVolume.ARuleDrawsTheChain
import YangMills.Construction.HullsInEveryVolume.EachTowerHasARuleOfTheNoises
import YangMills.Construction.HullsInEveryVolume.NoisesCarryTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChainNoise
open RenormalizationStepParameters HullTrees WeightedResponses
theorem noiseRepresentation (hR : existsNoiseRuleStatement) (hD : ruleDrawsChainStatement) :
    noiseRepresentationStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hdrawn _ _ _ _
  refine ⟨0, ?_⟩
  intro Kr _ _ _ _ _
  refine ⟨Tb.floorMin, ?_⟩
  intro y hy _ _ g β K m T hrun
  have hfit := hdrawn.fits y hy
  refine ⟨hR _ hfit T, ?_⟩
  intro rule hr u n _ hat
  have hside : n = 2 * Tb.side ^ m * Tb.side ^ (K - u) := by
    rw [hat.side_eq, torusSideAtLevel, fineSide_eq]
  have hLge : 2 ^ 16 ≤ Tb.side := hfit.L_ge
  have hn₀ : 4096 ≤ Tb.n₀ := hfit.n₀_ge
  have hvol : Tb.side * Tb.n₀ ≤ 2 * Tb.side ^ m := hrun.volume_le
  have hbig : 64 ≤ Tb.side * Tb.n₀ := by nlinarith
  have hm : m ≠ 0 := by
    rintro rfl
    simp only [pow_zero, mul_one] at hvol
    omega
  have hpos : 1 ≤ Tb.side ^ (K - u) := Nat.one_le_pow _ _ (by omega)
  have hL : (Tb.stepParameters y).side ∣ n := by
    rw [hside]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ hm) 2) _
  have h64 : 64 ≤ n := by
    rw [hside]
    exact (hbig.trans hvol).trans (Nat.le_mul_of_pos_right _ hpos)
  exact (hD _ hfit T rule β hrun.cutoff_bottom hrun.marks hr u n hL h64).2
end YangMills.Construction.ChainNoise
end
