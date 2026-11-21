import YangMills.Construction.ClusterExpansionOfAStep.FlowOfTheExpansion
import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.TheExpansionReturns
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import YangMills.Construction.TestFunctions.SeparatedBumpPairs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.WeightedResponses
def HoldsAtAdmissibleParameters (P : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop) : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : RenormalizationStepParameters.ChainParameters → ℝ), (∀ c, 0 < rt₀ c) ∧ ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.coupling = a → T.side = L → T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
      ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → StepReturn.ExpansionReturnsAt (T.stepParameters y) →
        (∀ β : ℝ, y ≤ β → TorusLumps.HasExpansion (T.stepParameters y) 0 β (TorusLumps.wilsonWeight β)) → P T y
def plaquetteBarycenterAt (L k m : ℕ) (p : TorusFields.TorusPlaquette (fineSide L k (2 * L ^ m))) :
    PeriodicLattice.FourTorus L m :=
  TorusMetric.torusProj (PeriodicLattice.torusSide L m) fun i =>
    (((p.1 i).val : ℝ) + (if i = p.2.1 then 1 / 2 else 0) + (if i = p.2.2 then 1 / 2 else 0)) / (L : ℝ) ^ k
def testWeight (L k m : ℕ) (f : PeriodicLattice.FourTorus L m → ℝ) : PlaquetteWeight (fineSide L k (2 * L ^ m)) :=
  fun p => f (plaquetteBarycenterAt L k m p)
def chainDepth (x : ℝ) : ℕ := ⌊Real.log x ^ 2⌋₊
structure InScaleWindow (ℓ : TorusLumps.StepParameters) (β : ℝ) (k m : ℕ) (n x₀ : ℝ) : Prop where
  le_coupling : x₀ ≤ (TorusLumps.couplingFlow ℓ β k).1
  flow_ge : ∀ j ≤ k + 2 * chainDepth (TorusLumps.couplingFlow ℓ β k).1, ℓ.y₁ ≤ (TorusLumps.couplingFlow ℓ β j).1
  lower_le : 2 ^ 12 * (ℓ.side : ℝ) * (TorusLumps.clusterRange (TorusLumps.couplingFlow ℓ β k).1 : ℝ) ≤ n
  le_upper : n ≤ (TorusLumps.couplingFlow ℓ β k).1 ^ ((1 : ℝ) / 90)
  side_ge : Real.exp (Real.log (TorusLumps.couplingFlow ℓ β k).1 ^ 3) ≤ 2 * (ℓ.side : ℝ) ^ m
def TowerFollowsFlow {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) (β : ℝ) (k : ℕ) : Prop :=
  ∀ j ≤ k + 1, (T.stage j).coupling = (TorusLumps.couplingFlow ℓ β j).1
def IsNormalizedPairAt (ℓ : TorusLumps.StepParameters) (m : ℕ) (n vt : ℝ) (f h : PeriodicLattice.FourTorus ℓ.side m → ℝ) :
    Prop :=
  (f, h) ∈ TestFunctions.separatedPairsFourTorus ℓ.side m n vt ∧ TestFunctions.uniformNorm f = 1 ∧
    TestFunctions.uniformNorm h = 1
end YangMills.Construction.WeightedResponses
end
