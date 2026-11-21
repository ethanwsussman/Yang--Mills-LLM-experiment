import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChainIsATotal
import YangMills.Construction.RunningCouplingSlope.TotalAtTheLeastField
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepIsATotal
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter
namespace YangMills.Construction
open YangMills.Construction.SlopeCoefficient
namespace RunningCouplingSlope.ChainLogarithmInduction
private theorem isGaugeTotalAt_chainLogarithm_zero (a ρ : ℝ) (L n : ℕ) :
    IsGaugeTotalAt (chainLogarithm a ρ L 0) n where
  contDiffAt_perturb := fun _ _ _ => contDiffAt_const
  gauge_invariant_near := Eventually.of_forall fun _ => rfl
  constant_gauge_invariant := fun _ => Eventually.of_forall fun _ => rfl
  isometry_invariant := fun _ => Eventually.of_forall fun _ _ _ => rfl
private theorem isGaugeTotalAt_chainLogarithm_succ {a ρ : ℝ} {L t n : ℕ}
    (hstep : IsGaugeTotalAt (stepGaugeTotal a ρ L t) n)
    (hmin : IsGaugeTotalAt (atMinimizer a ρ L t (chainLogarithm a ρ L t)) n) :
    IsGaugeTotalAt (chainLogarithm a ρ L (t + 1)) n where
  contDiffAt_perturb := fun k c X => (hstep.contDiffAt_perturb k c X).add (hmin.contDiffAt_perturb k c X)
  gauge_invariant_near := by
    filter_upwards [hstep.gauge_invariant_near, hmin.gauge_invariant_near] with p e e'
    exact congrArg₂ (· + ·) e e'
  constant_gauge_invariant := fun g => by
    filter_upwards [hstep.constant_gauge_invariant g, hmin.constant_gauge_invariant g] with V e e'
    exact congrArg₂ (· + ·) e e'
  isometry_invariant := fun g => by
    filter_upwards [hstep.isometry_invariant g, hmin.isometry_invariant g] with V e e' V' hc
    exact congrArg₂ (· + ·) (e V' hc) (e' V' hc)
theorem chainLogarithmIsGaugeTotal_of (hS : StepGaugeTotalIsGaugeTotal) (hM : GaugeTotalAtMinimizer) :
    ChainLogarithmIsGaugeTotal := by
  intro a ha L hL k ρ hρ hρ'
  induction k with
  | zero => exact Eventually.of_forall fun n => isGaugeTotalAt_chainLogarithm_zero a ρ L n
  | succ t ih =>
    filter_upwards [hS a ha L hL t ρ hρ hρ', hM a ha L hL t ρ hρ hρ' _ ih] with n e e'
    exact isGaugeTotalAt_chainLogarithm_succ e e'
end RunningCouplingSlope.ChainLogarithmInduction
end YangMills.Construction
end
