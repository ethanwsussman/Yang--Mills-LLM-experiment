import YangMills.Construction.FourPointCondition.FourPointBoundAlongTheFlow
import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
def CouplingNearOneLoopAt (p : TorusLumps.StepParameters) (Bs g : ℝ) : Prop :=
  ∀ room : ℕ → ℝ, RoomFunctions.IsSubexpGrowth room → ∃ (d₀ : ℝ) (η : ℝ → ℝ), d₀ ∈ Ioo (0 : ℝ) 1 ∧
    Tendsto η (𝓝[>] 0) (𝓝 0) ∧ ∀ (a : ℝ → ℕ → ℝ) (K : ℕ+) (β : ℝ),
      (FourPointCondition.flowProfile p g Bs room a).IsFirstPassage K β → ∀ d ∈ Ioc (0 : ℝ) d₀,
        (FourPointCondition.flowProfile p g Bs room a).IsDeepEnough p.side K 1 d →
          |(FourPointCondition.flowProfile p g Bs room a).coupling K β d ^ 2 * Real.log (1 / d) /
            FourPointCondition.oneLoopCoeff - 1| ≤ η d
structure FourPointLawOnWindowAt (p : TorusLumps.StepParameters) (Bs g : ℝ) : Prop where
  clause : FourPointCondition.FourPointConditionAtFlowData p Bs g
  coupling_near : CouplingNearOneLoopAt p Bs g
def fourPointLawOnWindow : Prop :=
  HoldsAtAdmissibleParameters fun T y => ∀ Bs : ℝ, 2 * T.B ≤ Bs → ForSmallCoupling fun g =>
    FourPointLawOnWindowAt (T.stepParameters y) Bs g
end YangMills.Construction.TotalDensities
end
