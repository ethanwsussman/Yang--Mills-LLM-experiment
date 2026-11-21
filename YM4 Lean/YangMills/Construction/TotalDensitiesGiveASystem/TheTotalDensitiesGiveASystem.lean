import YangMills.Construction.TotalDensitiesGiveASystem.TheExpansionFlowIsTheTotalFlow
import YangMills.Construction.TotalDensitiesGiveASystem.TheFourPointLawInTheLimits
import YangMills.Construction.TotalDensitiesGiveASystem.TheFourPointLawOnTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.TheLawOfTheTrajectoryIsTheLawOfTheChain
import YangMills.Construction.TotalDensitiesGiveASystem.TheWindowHasItsData
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
open RenormalizationStepParameters TorusLumps SystemsWithFiveBounds
structure IsSystemOfFlow (Y : FiveBoundSystem) (ℓ : TorusLumps.StepParameters) (Bs top M ϑ : ℝ) : Prop where
  side_eq : Y.L = ℓ.side
  scale_eq : Y.M = M
  shape_eq : Y.ϑ = ϑ
  top_eq : Y.top = top
  isPair_iff : ∀ g ∈ Ioc 0 top, ∀ (K : ℕ+) (β : ℝ), Y.IsPair g K β ↔ IsFirstPassagePoint ℓ Bs g K β
  states_eq : ∀ (K : ℕ+) (β : ℝ), Y.States Y.L K β = InfiniteLattice.periodicGibbsSet Y.L K β
def FlowDataAtParameters (T : ParameterAssignment) (y : ℝ) : Prop :=
  T.floorMin ≤ y ∧ (T.stepParameters y).Admissible ∧ FlowIsChainLaw (T.stepParameters y) ∧
    ∀ Bs : ℝ, 2 * T.B ≤ Bs → ∃ c₅ lam top : ℝ, 0 ≤ c₅ ∧ 0 < lam ∧ 0 < top ∧
      (∀ g ∈ Ioc 0 top, y ≤ g ^ (-2 : ℤ) ∧
        TotalDensitiesGiveASystem.PassageWindowData (T.stepParameters y) Bs c₅ lam g ∧
        ExpansionFlowEqTotalFlowAt (T.stepParameters y) Bs g ∧ FourPointLawOnWindowAt (T.stepParameters y) Bs g) ∧
      ∀ (m : ℕ) (ϑ : ℝ), ϑ ∈ Ioc (0 : ℝ) 1 → ϑ ≤ TwoPoints.Shapes.shapeConst →
        ∃ Y : FiveBoundSystem, IsSystemOfFlow Y (T.stepParameters y) Bs top ((T.side : ℝ) ^ m) ϑ ∧
          ∀ g ∈ Ioc 0 top, FourPointLawInLimitsAt Y.L (Y.IsPair g)
def SystemFromTotalDensities : Prop := HoldsAtAdmissibleParameters FlowDataAtParameters
end YangMills.Construction.TotalDensities
end
