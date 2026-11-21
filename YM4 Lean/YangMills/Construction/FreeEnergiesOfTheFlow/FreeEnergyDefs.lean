import YangMills.Construction.ClusterExpansionOfAStep.ColdRenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.ClusterExpansionOfAStep.TheExpansionReturns
import YangMills.Construction.ClusterExpansionOfAStep.TheFlowIsTheLawOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeEnergies
def torusPartition (ℓ : TorusLumps.StepParameters) (β : ℝ) (t n : ℕ) [NeZero n] : ℝ :=
  ClusterExpansionOfAStep.wilsonPartition β (WeightedResponses.fineSide ℓ.side t n)
def flowFunctionalAtTrivial (ℓ : TorusLumps.StepParameters) (β : ℝ) (t n : ℕ) : ℝ :=
  ClusterExpansionOfAStep.flowFunctional ℓ β t n (TorusFields.trivialField n)
structure ExpansionHolds (ℓ : TorusLumps.StepParameters) : Prop where
  returns_at : StepReturn.ExpansionReturnsAt ℓ
  wilson_expansion : ∀ β : ℝ, ℓ.y₁ ≤ β → TorusLumps.HasExpansion ℓ 0 β (TorusLumps.wilsonWeight β)
def CouplingsAboveFloor (ℓ : TorusLumps.StepParameters) (β : ℝ) (t : ℕ) : Prop :=
  ∀ j ≤ t, ℓ.y₁ ≤ ClusterExpansionOfAStep.flowCoupling ℓ β j
def HoldsForAdmissibleParameters (P : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop) : Prop :=
  ∃ rt₀ : RenormalizationStepParameters.ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible →
    T.ColdStepHolds → T.rt ≤ rt₀ T.toChainParameters → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
      ExpansionHolds (T.stepParameters y) → P T y
structure IsFlowStep (T : RenormalizationStepParameters.ParameterAssignment) (y β : ℝ) (s : ℕ) (R : StepSettings.StepSetup) : Prop where
  onFamily : R.OnParameters T y
  depth_eq : R.depth = s
  coupling_eq : R.coupling = ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β s
  nextCoupling_eq : R.nextCoupling = ClusterExpansionOfAStep.flowCoupling (T.stepParameters y) β (s + 1)
  functional_eq : R.functional = ClusterExpansionOfAStep.flowFunctional (T.stepParameters y) β s
def blockActivityAtTrivial (lam : ℝ) (R : StepSettings.StepSetup) (n : ℕ) [NeZero n]
    (Y : TorusFields.TorusSite n) : ℝ :=
  (StepSettings.coldChartSetting R (TorusFields.trivialField n)).blockActivity lam Y +
    R.blockDensityAt Y (TorusFields.trivialField n)
end YangMills.Construction.FreeEnergies
end
