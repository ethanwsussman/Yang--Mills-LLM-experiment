import YangMills.Construction.SystemsWithFiveBounds.SystemWithFiveBounds
import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
structure PassageWindowData (ℓ : TorusLumps.StepParameters) (Bs c₅ lam g : ℝ) : Prop where
  passes_from : ∀ β : ℝ, SequencePassage.passageThreshold Bs g ≤ β →
    ∃ K : ℕ, TotalDensities.IsFirstPassagePoint ℓ Bs g K β
  cutoff_bounds : ∀ (K : ℕ) (β : ℝ), TotalDensities.IsFirstPassagePoint ℓ Bs g K β →
    (β - g ^ (-2 : ℤ)) / Bs - 1 ≤ K ∧ (K : ℝ) ≤ 1 + (β - g ^ (-2 : ℤ) - Bs + c₅) / lam
  coupling_gt : ∀ (K : ℕ) (β : ℝ), TotalDensities.IsFirstPassagePoint ℓ Bs g K β →
    ∀ k ≤ K, g ^ (-2 : ℤ) < ClusterExpansionOfAStep.flowCoupling ℓ β k
  infinite_cutoffs : {K : ℕ | ∃ β, TotalDensities.IsFirstPassagePoint ℓ Bs g K β}.Infinite
  slope_tendsto : ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ (K : ℕ) (β : ℝ), 1 ≤ K →
    TotalDensities.IsFirstPassagePoint ℓ Bs g K β →
    |β / Real.log (1 / PeriodicLattice.meshSize ℓ.side (K : ℤ)) -
      SystemsWithFiveBounds.asymptoticFreedomSlope| ≤ δ K
def passageWindowDataStatement : Prop :=
  TotalDensities.HoldsAtAdmissibleParameters fun T y => ∀ Bs : ℝ, 2 * T.B ≤ Bs → ∃ c₅ : ℝ, 0 ≤ c₅ ∧
    TotalDensities.ForSmallCoupling fun g => PassageWindowData (T.stepParameters y) Bs c₅
      (3 / 4 * (SystemsWithFiveBounds.asymptoticFreedomSlope * Real.log T.side)) g
end YangMills.Construction.TotalDensitiesGiveASystem
end
