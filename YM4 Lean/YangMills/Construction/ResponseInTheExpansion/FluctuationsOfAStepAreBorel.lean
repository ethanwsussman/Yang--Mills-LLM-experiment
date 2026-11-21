import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.RenormalizationStepParameters YangMills.Construction.MarkedIntegrals YangMills.Construction.WeightedResponses
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (y : ℝ)
def stepDeviationMeasurableAt : Prop :=
  ∃ x₀ : ℝ, ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (nn : ℝ) (j : ℕ) (o : TorusSite n),
    IsLocalChainAbove Tb y T β k n nn x₀ → j < 2 * localChainDepth (Tb.stepParameters y) β k →
    (∀ (b : TorusBond (n * (Tb.stepParameters y).side)) (a : Fin 3),
      b ∈ chartBondsInBlocks (Tb.stepParameters y).side (supBall o ((localBlockSide (Tb.stepParameters y) β k : ℝ) / 8)) →
      Measurable (Set.indicator
        {p : TorusField n × TorusField (n * (Tb.stepParameters y).side) |
          IsColdOnBall (Tb.stepParameters y).threshold p.1 o (localBlockSide (Tb.stepParameters y) β k)}
        fun p => imaginaryComponent a (stepDeviation T (k + j) p.1 p.2 b))) ∧
    MeasurableSet {u : MarkedSample (Tb.stepParameters y) (k + j + 1) n |
      Disjoint (stageState T (k + j + 1) n u).2.1 (supBall o (localBlockSide (Tb.stepParameters y) β k)) ∧
        StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) o u}
def stepDeviationMeasurableStatement : Prop := HoldsOnParameterFamilies stepDeviationMeasurableAt
end YangMills.Construction.ResponseInTheExpansion
end
