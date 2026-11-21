import YangMills.Construction.ClusterExpansionOfAStep.TheFlowIsTheLawOfTheChain
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction.DensitySupply
def toCoordFun (φ : TestFunctions.EuclideanFourSpace → ℝ) : (Fin 4 → ℝ) → ℝ := fun x => φ (WithLp.toLp 2 x)
def rescaled (L K s : ℕ) (φ : TestFunctions.EuclideanFourSpace → ℝ) (x : InfiniteLattice.AmbientSpace) : ℝ :=
  φ (WithLp.toLp 2 fun a => (L : ℝ) ^ K / (L : ℝ) ^ s * x a)
abbrev flowSequence (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) : ℝ → ℕ → ℝ := ClusterExpansionOfAStep.flowCoupling (T.stepParameters y)
def MomentPointsExist (T : RenormalizationStepParameters.ParameterAssignment) (Kr : WeightedResponses.ResponseParameters) (y : ℝ) : Prop :=
  ∀ g : ℝ, 0 < g → y ≤ (g ^ 2)⁻¹ → ∀ (k : ℕ) [NeZero k], 2 ≤ k → k ≤ 8 → ∀ R d : ℝ, 0 < d →
    ∀ (P : LevelTestFunctions.LevelData k) (β : ℝ), P.SupAdmissible (T.stepParameters y).side R d →
      (T.stepParameters y).side * (T.stepParameters y).n₀ ≤ P.period (T.stepParameters y).side →
      WeightedResponses.couplingWindowTop (T.stepParameters y) g ≤ β →
      WeightedResponses.IsFirstPassage (T.stepParameters y)
        (WeightedResponses.couplingWindowTop (T.stepParameters y) g) β P.windowLevel →
      ∃ S : MomentLaw.MomentPoint ⟨T, Kr, y, g, k, R, d⟩, S.data = P ∧ S.β = β
end YangMills.Construction.DensitySupply
end
