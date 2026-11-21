import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.StageDensity
open WeightedResponses ResponseInTheExpansion TorusLumps TorusFields RenormalizationStepParameters
def stageStateDensityStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n],
    IsTowerAtParameters Tb y T β k → T.MarksMeasurable → IsBlockTorusSide (Tb.stepParameters y) n →
    ∀ G : StageState T k n → ENNReal, Measurable G →
      ENNReal.ofReal (∫ W, wilsonWeight β (fineSide (Tb.stepParameters y).side k n) W
          ∂(fieldHaar (fineSide (Tb.stepParameters y).side k n))) *
        ∫⁻ u, G (stageState T k n u) ∂(markedSampleLaw T β k n) =
      ∫⁻ W, (open Classical in
        ∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange (T.stage k).coupling) W),
          ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage k).labelWeight n W Y ω)
            ∂(Measure.pi fun _ : Y => (T.stage k).labels.μ)) ∂(fieldHaar n)
end YangMills.Construction.StageDensity
end
