import YangMills.Construction.ClusterExpansionOfAStep.ColdRenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.FlowOfTheExpansion
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.ClusterExpansionOfAStep.TheExpansionReturns
import YangMills.Construction.ResponseInTheExpansion.ColdConditionsOfAResponse
import YangMills.Construction.ResponseInTheExpansion.ColdRegimeBounds
import YangMills.Construction.ResponseInTheExpansion.ResponsesOfTheExpansion
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
variable {ℓ : TorusLumps.StepParameters}
def HoldsOnParameterFamilies (P : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop) : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : RenormalizationStepParameters.ChainParameters → ℝ) (C₀ : ℝ), (∀ c, 0 < rt₀ c) ∧ ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.coupling = a → T.side = L → T.Admissible → T.ColdStepHolds →
      T.HoldsFrom WeightedResponses.ColdRegimeEstimatesAt →
      T.rt ≤ rt₀ T.toChainParameters → C₀ ≤ T.derivBound →
      ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → StepReturn.ExpansionReturnsAt (T.stepParameters y) →
        (∀ β : ℝ, y ≤ β → TorusLumps.HasExpansion (T.stepParameters y) 0 β (TorusLumps.wilsonWeight β)) → P T y
def flowCouplings (ℓ : TorusLumps.StepParameters) (β : ℝ) : ℕ → ℝ := fun j => (TorusLumps.couplingFlow ℓ β j).1
structure IsChainResponseCoeff (ℓ : TorusLumps.StepParameters) (K : WeightedResponses.ResponseParameters) (β : ℝ) (k : ℕ)
    (α : ℕ → ℝ) : Prop where
  zero_eq : α 0 = 1
  bounds : ∀ j ≤ k, ∃ Ra Rb : TorusLumps.LocalDensity,
    WeightedResponses.ColdResponseBounds ℓ K j (flowCouplings ℓ β j) (α j)
      (coldResponseChain ℓ β (flowCouplings ℓ β) α j) Ra Rb
structure StageTower.StartsAtWilson (T : WeightedResponses.StageTower ℓ) (β : ℝ) : Prop where
  depth_eq : T.base.depth = 0
  functional_eq : T.base.functional = TorusLumps.wilsonWeight β
  eq_basePoint : ∀ ω : T.base.labels.Ω, ω = T.basePoint
  measure_basePoint : T.base.labels.μ {T.basePoint} = 1
  labelWeight_eq : ∀ (n : ℕ) [NeZero n] (W : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n))
    (ω : Y → T.base.labels.Ω),
    T.base.labelWeight n W Y ω =
      open Classical in
      if Y = TorusLumps.thickening (2 * TorusLumps.clusterRange T.base.coupling) (TorusLumps.torusHotSites ℓ W) then
        TorusLumps.wilsonWeight β n W else 0
structure IsTowerAtParameters (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (T : WeightedResponses.StageTower (Tb.stepParameters y))
    (β : ℝ) (k : ℕ) : Prop where
  startsAtWilson : StageTower.StartsAtWilson T β
  coupling_eq : ∀ j ≤ k + 1, (T.stage j).coupling = (TorusLumps.couplingFlow (Tb.stepParameters y) β j).1
  onFamily : ∀ j ≤ k, (T.stage j).toStepSetup.OnParameters Tb y
end YangMills.Construction.ResponseInTheExpansion
end
