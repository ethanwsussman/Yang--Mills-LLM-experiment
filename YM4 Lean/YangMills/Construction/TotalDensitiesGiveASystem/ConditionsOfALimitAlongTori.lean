import YangMills.Construction.TotalDensitiesGiveASystem.ConditionsOfTheMainStatement
import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
def GrowingTorusLimitsSatisfyConditions : Prop :=
  TotalDensities.HoldsAtAdmissibleParameters fun T y => TotalDensities.ForSmallCoupling fun g =>
    ∃ (k : ℕ) (c₁ c₂ κ : ℝ), ∀ C : SystemsWithFiveBounds.LimitConstants,
    C.Valid → k ≤ C.schwartzOrder → c₁ ≤ C.schwartzPrefactor → c₂ ≤ C.schwartzBase → κ ≤ C.schwartzExp →
    TotalDensitySystem.LocalCumulantBounds (T.stepParameters y) (2 * T.B) g C →
    ∀ (ϑ d₀ : ℝ) (ηBar εBar : ℝ → ℝ), ϑ ∈ Ioc (0 : ℝ) 1 →
      TotalDensities.TwoPointLawInLimits (T.stepParameters y) (2 * T.B) g ϑ d₀ ηBar εBar →
      d₀ ∈ Ioc (0 : ℝ) (1 / 40) → (∀ d ∈ Ioc 0 d₀, ηBar d ∈ Icc (0 : ℝ) (1 / 3)) →
      (∀ d ∈ Ioc 0 d₀, εBar d ∈ Icc (0 : ℝ) (1 / 2)) → ∀ S : LimitTheorem.CumulantFamily,
        TotalDensitySystem.IsGrowingTorusLimit (T.stepParameters y) (2 * T.B) g S →
        TotalDensitySystem.LimitRequirements ϑ d₀ ηBar C S
end YangMills.Construction.TotalDensities
end
