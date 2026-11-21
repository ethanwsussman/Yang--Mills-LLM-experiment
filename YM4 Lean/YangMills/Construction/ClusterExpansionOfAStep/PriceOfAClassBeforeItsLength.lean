import YangMills.Construction.ClusterExpansionOfAStep.CountsOfAClassAtAStep
import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfTheImageForm
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields TorusLumps StepSettings RenormalizationStepParameters StepCosts
def componentExponent (R : StepSetup) (cE CE : ℝ) {n : ℕ} [NeZero n] (V : TorusField n) (P : Finset (Finset (TorusSite n)))
    (W : TorusField (n * R.params.side)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) : ℝ :=
  -R.coupling * (6 * R.params.κ * R.params.threshold ^ 2 *
        ((open Classical in (torusHotLumps R.params V).filter (· ⊆ P.biUnion id)).card : ℝ) +
      R.params.κ / 4 * R.params.threshold ^ 2 *
        (hotLumpsInAttached R.params R.range W bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ) +
      cE * (badBlocksInAttached R.params R.range bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ) +
      R.params.κ₁ * R.params.threshold ^ 2 *
        (lengthInAttached R.params R.range W bad Yt (hotCoreSites R V) (P.biUnion id) : ℝ)) +
    CE * (R.range : ℝ) ^ 8 * Real.log R.coupling * ((nearSites R.nextRange (P.biUnion id)).card : ℝ)
def ComponentPriceBound : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ CE y₀ : ℝ, 0 ≤ CE ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.IsWellPosed → R.nextCoupling = R.shiftedCoupling T.lam → |R.nextCoupling - R.coupling| ≤ 2 * R.params.B →
    ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (V : TorusField n) (Y : Finset (TorusSite n))
      (ω : Y → CoarseLabel R.labels.Ω R.params.side) (P : Finset (Finset (TorusSite n))),
      IsHullState R.params R.nextRange V Y → P ⊆ chainComponents R.nextRange Y →
      (∀ X ∈ chainComponents R.nextRange Y \ P, coarseFactorExpansion R n V Y ω X ≠ 0) →
      ∀ M : ℝ, (∀ (ν : ↥(P.biUnion id) → CoarseLabel R.labels.Ω R.params.side) (W : TorusField (n * R.params.side))
          (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
          (bad : Finset (TorusBond (n * R.params.side)))
          (b : BaseChoice R.params.side n), IsHullState R.params R.range W Yt →
          coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = ⟨Y, glueLabel Y (P.biUnion id) ω ν⟩ →
          componentExponent R T.cE CE V P W bad Yt ≤ M) →
      (open Classical in
        ∫⁻ ν, (if ∃ X ∈ P, coarseFactorExpansion R n V Y (glueLabel Y (P.biUnion id) ω ν) X = 0 then 0 else
          ENNReal.ofReal ((∏ X ∈ P, coarseFactorExpansion R n V Y (glueLabel Y (P.biUnion id) ω ν) X) *
            Real.exp (∑ z ∈ Finset.univ.filter (fun z : TorusSite n =>
                ∃ u ∈ P.biUnion id, (supDist z u : ℝ) < (R.nextRange : ℝ) / 4),
              R.stateDensity T.lam n z V Y (glueLabel Y (P.biUnion id) ω ν))))
          ∂(Measure.pi fun _ : (P.biUnion id : Finset (TorusSite n)) => coarseLabelMeasure R.labels.μ R.params.side)) ≤
        ENNReal.ofReal (Real.exp M)
end YangMills.Construction.ClusterExpansionOfAStep
end
