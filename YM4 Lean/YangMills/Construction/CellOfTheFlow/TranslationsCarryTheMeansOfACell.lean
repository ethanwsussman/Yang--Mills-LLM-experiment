import YangMills.Construction.CellOfTheFlow.NoiseOfTheChain
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps RenormalizationStepParameters WeightedResponses
def translationCarriesCellMeansStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y =>
    ∀ (T : StageTower (Tb.stepParameters y)) (S : ChainSampler T) (β s₀ s₁ : ℝ) (k e : ℕ),
    IsTowerAtParametersMeasurable Tb y T β k → (∀ s, (S s).IsFaithful) →
    (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ ≤ 2 * (Tb.stepParameters y).side ^ e →
    ∀ (v : Fin 4 → ℤ), (∀ i, ((Tb.stepParameters y).side : ℤ) ∣ v i) →
    ∀ (c : Finset (TorusSite (2 * (Tb.stepParameters y).side ^ e)))
      (U : TorusField (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ e))),
      lowerSumExpMean T S s₀ s₁ k _ c
          (TorusFields.translate (siteOfInt fun i => ((Tb.stepParameters y).side : ℤ) ^ k * v i) U) =
        lowerSumExpMean T S s₀ s₁ k _ (c.image (· + siteOfInt v)) U ∧
      cellEventProb T S k _ c
          (TorusFields.translate (siteOfInt fun i => ((Tb.stepParameters y).side : ℤ) ^ k * v i) U) =
        cellEventProb T S k _ (c.image (· + siteOfInt v)) U
end YangMills.Construction.CellWindows
end
