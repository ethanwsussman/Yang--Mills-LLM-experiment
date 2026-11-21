import YangMills.Construction.ClusterExpansionOfAStep.PriceOfAClassBeforeItsLength
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
def scoredComponentPriceBound : Prop :=
  ∃ rt₀ : RenormalizationStepParameters.ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∀ s₁ : ℝ, 0 ≤ s₁ → ∃ CE y₀ : ℝ, 0 ≤ CE ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSettings.StepSetup, R.OnParameters T y →
    R.IsWellPosed → R.nextCoupling = R.shiftedCoupling T.lam → |R.nextCoupling - R.coupling| ≤ 2 * R.params.B →
    ∀ s : R.labels.Ω → ℝ,
      WeightedResponses.PriceBoundsScore R.params R.coupling R.labels R.clusterFactor R.siteDensity s →
    ∀ (n : ℕ) [NeZero n], TorusLumps.IsBlockTorusSide R.params n →
      ∀ (V : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n))
        (ω : Y → TorusLumps.CoarseLabel R.labels.Ω R.params.side) (P : Finset (Finset (TorusFields.TorusSite n))),
      TorusLumps.IsHullState R.params R.nextRange V Y → P ⊆ TorusLumps.chainComponents R.nextRange Y →
      (∀ X ∈ TorusLumps.chainComponents R.nextRange Y \ P, StepSettings.coarseFactorExpansion R n V Y ω X ≠ 0) →
      ∀ M : ℝ, (∀ (ν : ↥(P.biUnion id) → TorusLumps.CoarseLabel R.labels.Ω R.params.side)
          (W : TorusFields.TorusField (n * R.params.side))
          (Yt : Finset (TorusFields.TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
          (bad : Finset (TorusFields.TorusBond (n * R.params.side)))
          (b : StepCosts.BaseChoice R.params.side n), TorusLumps.IsHullState R.params R.range W Yt →
          StepSettings.coarseStateOf R (StepSettings.hotCoreSites R V) W Yt ωt bad b =
            ⟨Y, TorusLumps.glueLabel Y (P.biUnion id) ω ν⟩ →
          ClusterExpansionOfAStep.componentExponent R T.cE CE V P W bad Yt ≤ M) →
      (open Classical in
        ∫⁻ ν, (if ∃ X ∈ P, StepSettings.coarseFactorExpansion R n V Y (TorusLumps.glueLabel Y (P.biUnion id) ω ν) X = 0
          then 0 else
          ENNReal.ofReal ((∏ X ∈ P, StepSettings.coarseFactorExpansion R n V Y (TorusLumps.glueLabel Y (P.biUnion id) ω ν) X) *
            Real.exp (∑ z ∈ Finset.univ.filter (fun z : TorusFields.TorusSite n =>
                ∃ u ∈ P.biUnion id, (TorusFields.supDist z u : ℝ) < (R.nextRange : ℝ) / 4),
              R.stateDensity T.lam n z V Y (TorusLumps.glueLabel Y (P.biUnion id) ω ν)) *
            Real.exp (∑ y : (P.biUnion id : Finset (TorusFields.TorusSite n)),
              WeightedResponses.coarseLabelScore s₁ s (ν y))))
          ∂(Measure.pi fun _ : (P.biUnion id : Finset (TorusFields.TorusSite n)) =>
              TorusLumps.coarseLabelMeasure R.labels.μ R.params.side)) ≤
        ENNReal.ofReal (Real.exp M)
end YangMills.Construction.ResponseInTheExpansion
end
