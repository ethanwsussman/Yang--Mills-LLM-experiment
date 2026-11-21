import YangMills.Construction.RunningCouplingSlope.CoefficientsAdd
import YangMills.Construction.RunningCouplingSlope.CoefficientsOfTheChainAdd
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficient
import YangMills.Construction.RunningCouplingSlope.LeastFieldIsABlockMap
import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChainIsATotal
import YangMills.Construction.RunningCouplingSlope.StepTotalsHaveCoefficients
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Conventions SlopeCoefficient
namespace RunningCouplingSlope
theorem chainSlopeCoefficientsAdd (hC : PullbackKeepsSlopeCoefficient)
    (hP : MinimizerIsBlockMap) (hS : StepGaugeTotalsHaveSlopeCoefficients)
    (hT : ChainLogarithmIsGaugeTotal) (hAdd : SlopeCoefficientAdditive) :
    ChainSlopeCoefficientsAdd := by
  intro a L hD
  have ha : 0 < a := by
    obtain ⟨T, hE, rfl, -⟩ := hD
    linarith [hE.a_ge]
  have hL : IsAdmissibleBlockingFactor L := by
    obtain ⟨T, hE, -, rfl⟩ := hD
    exact ⟨hE.L_odd, le_trans (by norm_num) hE.L_ge⟩
  have hL0 : 0 < L := by have := hL.2; omega
  choose b hb using hS a L hD
  refine ⟨b, fun t ρ h0 h1 => hb t ρ h0 h1, fun k ρ h0 h1 => ?_⟩
  induction k with
  | zero =>
    rw [Finset.sum_range_zero]
    exact hAdd.2.1
  | succ k ih =>
    obtain ⟨P, Pl, hbm⟩ := hP a ha L hL k ρ h0 h1
    have hpull : HasSlopeCoefficient Filter.atTop
        (pullbackTotal (chainLogarithm a ρ L k) (minimizerOnFinerTorus a ρ L k))
        (∑ l ∈ Finset.range k, b l) := by
      refine hC L _ _ P Pl _ hL0 hbm ih ?_
      have htot := hT a ha L hL (k + 1) ρ h0 h1
      have hst : ∀ᶠ n in Filter.atTop, IsGaugeTotalAt (stepGaugeTotal a ρ L k) n := by
        obtain ⟨K, hK, -⟩ := hb k ρ h0 h1
        exact hK.eventually_isGaugeTotalAt
      filter_upwards [htot, hst] with n h₁ h₂
      exact hAdd.2.2 _ _ n h₁ h₂
    have hsum := hAdd.1 _ _ _ _ (hb k ρ h0 h1) hpull
    have e : ∑ l ∈ Finset.range (k + 1), b l = b k + ∑ l ∈ Finset.range k, b l := by
      rw [Finset.sum_range_succ, add_comm]
    rw [e]
    exact hsum
end RunningCouplingSlope
end YangMills.Construction
end
