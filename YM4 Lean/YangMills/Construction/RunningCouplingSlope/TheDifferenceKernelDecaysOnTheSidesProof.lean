import YangMills.Construction.RunningCouplingSlope.DistanceOfTwoCells
import YangMills.Construction.RunningCouplingSlope.TheDifferenceKernelDecaysOnTheSides
import YangMills.Construction.RunningCouplingSlope.TheKernelOfTheDifferenceIsSmallOnASideForm
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
theorem differenceKernelDecaysUniformly_of_largeTori (hsmall : DifferenceKernelDecaysOnLargeTori)
    (hdist : CellDistLowerBound) : DifferenceKernelDecaysUniformly := by
  intro a ha L hL k hk
  obtain ⟨θ, C, hθ, hC, H⟩ := hsmall a ha L hL
  refine ⟨θ / 2, C, by positivity, hC, ?_⟩
  obtain ⟨n₀, Hn⟩ := H k hk
  have hLpos : 0 < L := by have := hL.2; omega
  filter_upwards [eventually_ge_atTop n₀, eventually_gt_atTop 0] with n hn₀ hn x
  refine (Hn n hn₀ hn _).trans ?_
  have hcoord : ∀ μ, |centredCoords x μ| ≤ (L : ℤ) ^ n := by
    intro μ
    haveI : NeZero (2 * L ^ n) := ⟨by positivity⟩
    have habs : (x μ).valMinAbs.natAbs ≤ (2 * L ^ n) / 2 := ZMod.natAbs_valMinAbs_le _
    have hhalf : (2 * L ^ n) / 2 = L ^ n := by omega
    rw [hhalf] at habs
    have hcast : ((x μ).valMinAbs.natAbs : ℤ) = |(x μ).valMinAbs| := Int.natCast_natAbs _
    change |(x μ).valMinAbs| ≤ _
    rw [← hcast]
    exact_mod_cast habs
  have hcell := hdist L n k hLpos _ hcoord
  have hexp : θ / 2 * ∑ μ, |(centredCoords x μ : ℝ)| ≤
      θ * cellDist (cellOfCoords L n k 0) (cellOfCoords L n k (centredCoords x)) := by nlinarith
  gcongr
end YangMills.Construction.RunningCouplingSlope
end
