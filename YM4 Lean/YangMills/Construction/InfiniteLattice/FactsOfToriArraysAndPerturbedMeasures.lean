import YangMills.Construction.InfiniteLattice.PropertiesOfToriArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def ToriArraysAndTiltedMeasuresFacts : Prop :=
  ∀ β : ℝ, 0 < β →
    (∀ (a : ℝ), 0 < a → ∀ Γ : PeriodSublattice a,
      Γ.IsFaithfulQuotient ∧ Γ.LiftIsFaithful ∧ Γ.GibbsMeasuresAreProbability β) ∧
    (∀ (𝔸 : LocalObservableArray) (t : ℝ),
      𝔸.SupportsLocallyFinite ∧ 𝔸.TiltedKernelWellDefined β t ∧
        ∀ Γ : PeriodSublattice 1, 𝔸.FitsPeriods Γ → 𝔸.PeriodicDescentWellDefined Γ β t) ∧
    CubicSublatticesInsideSubgroups ∧
    ∀ d : Conventions.StandingParameters, CubicTorusLiftsPeriodically d β
end InfiniteLattice
end YangMills.Construction
