import YangMills.Construction.RunningCouplingSlope.DistanceOfTwoCells
import YangMills.Construction.RunningCouplingSlope.LimitOfTheKernelOfTheDifference
import YangMills.Construction.RunningCouplingSlope.TheKernelOfTheDifferenceDecays
import YangMills.Construction.RunningCouplingSlope.TheKernelOfTheDifferenceIsSmallOnASideForm
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
theorem differenceKernelExpDecay_of_limit (hsmall : DifferenceKernelDecaysOnLargeTori)
    (hlim : DifferenceKernelLimitExists.Claim) (hdist : CellDistLowerBound) :
    DifferenceKernelExpDecay := by
  intro a ha L hL
  obtain ⟨θ, C, hθ, hC, H⟩ := hsmall a ha L hL
  refine ⟨θ / 2, C, by positivity, hC, fun k hk => ?_⟩
  obtain ⟨n₀, Hn⟩ := H k hk
  obtain ⟨κ, hκ⟩ := hlim a ha L hL k hk
  refine ⟨κ, hκ, fun z => ?_⟩
  have hLgt : (1 : ℤ) < (L : ℤ) := by
    have := hL.2
    exact_mod_cast (by omega : 1 < L)
  have hLpos : 0 < L := by have := hL.2; omega
  have hpow : Tendsto (fun n : ℕ => (L : ℤ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hLgt
  have hcoord : ∀ᶠ n : ℕ in atTop, ∀ μ, |z μ| ≤ (L : ℤ) ^ n :=
    eventually_all.mpr fun μ => hpow.eventually_ge_atTop _
  have hev : ∀ᶠ n : ℕ in atTop, |differenceKernelFinite a L n k z| ≤
      C * Real.exp (-(θ / 2 * ∑ μ, |(z μ : ℝ)|)) := by
    filter_upwards [hcoord, eventually_ge_atTop n₀, eventually_gt_atTop 0] with n hz hn₀ hn
    refine (Hn n hn₀ hn z).trans ?_
    have hcell := hdist L n k hLpos z hz
    have hexp : θ / 2 * ∑ μ, |(z μ : ℝ)| ≤
        θ * cellDist (cellOfCoords L n k 0) (cellOfCoords L n k z) := by nlinarith
    gcongr
  exact le_of_tendsto ((hκ z).abs) hev
end YangMills.Construction.RunningCouplingSlope
end
