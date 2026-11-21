import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import YangMills.Construction.TotalDensitiesGiveASystem.LawsOfTheTopStatement
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
structure IsLawModulus (d₁ : ℝ) (η₁ : ℝ → ℝ) : Prop where
  monotoneOn : MonotoneOn η₁ (Ioc 0 d₁)
  mem_Icc : ∀ d ∈ Ioc 0 d₁, η₁ d ∈ Icc (0 : ℝ) (1 / 3)
  tendsto : Tendsto η₁ (𝓝[>] 0) (𝓝 0)
def LawsAtEveryShape : Prop :=
  TotalDensities.HoldsAtAdmissibleParameters fun T y => ∃ c : ℝ, ∀ c₅ : ℝ, c ≤ c₅ →
    TotalDensities.ForSmallCoupling fun g =>
    ∀ ϑ ∈ Ioc (0 : ℝ) 1, ∀ room : ℕ → ℝ, RoomFunctions.IsSubexpGrowth room →
      ∀ (d₁ : ℝ) (η₁ : ℝ → ℝ), 0 < d₁ → IsLawModulus d₁ η₁ →
        ∃ (d₀ : ℝ) (ηBar εBar : ℝ → ℝ) (ζ : ℕ+ → ℝ → ℝ → ℝ) (K₀ : ℝ → ℕ) (d₄ : ℝ), d₀ ≤ d₁ ∧
          (∀ d ∈ Ioc 0 d₀, η₁ d ≤ ηBar d) ∧
          TotalDensities.TwoPointLawAtShape (T.stepParameters y) (2 * T.B) c₅
            (3 / 4 * TotalDensitySystem.oneLoopShift T.side) g ϑ room d₀ ηBar εBar ζ K₀ ∧
          TotalDensities.TwoPointLawInLimits (T.stepParameters y) (2 * T.B) g ϑ d₀ ηBar εBar ∧
          d₄ ∈ Ioc (0 : ℝ) d₀ ∧
          FourPointCondition.FourPointConditionHolds
            (TotalDensitySystem.totalFlowValue (T.stepParameters y) g (2 * T.B) room ζ)
            (T.stepParameters y).side ϑ d₄ 1 ∧
          TotalDensities.FourPointLawInLimits (T.stepParameters y) (2 * T.B) g ϑ d₄
end YangMills.Construction.TotalDensities
end
